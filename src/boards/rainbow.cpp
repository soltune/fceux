/* FCE Ultra - NES/Famicom Emulator
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 */

// NES 2.0 mapper 682 - Rainbow board by Broke Studio.
//
// Based on the Mesen2 implementation (Core/NES/Mappers/Homebrew/Rainbow.cpp)
// and the Broke Studio FCEUX fork (rainbow-stable branch).
//
// Supported: PRG/CHR banking, PRG-RAM, FPGA-RAM, nametable sources, fill mode,
// extended attributes/background tiles, scanline IRQ (with jitter counter),
// CPU cycle IRQ, NMI/IRQ vector redirection, VRC6-like audio read back
// through $4011 and FPGA-RAM auto read/write.
// Not supported: ESP/Wi-Fi, flash saving, window split, extended sprites,
// OAM helper functions and expansion audio output pins.

#include "mapinc.h"
#include "../ines.h"

#define PPUON (PPU[1] & 0x18)


extern uint8 **VPageR;

static uint8 *WRAM = NULL;
static uint32 WRAMSIZE = 0;
static uint8 *FPGA_RAM = NULL;
#define FPGA_RAMSIZE 0x2000
static uint8 *CHRRAM = NULL;
static uint32 CHRRAMSIZE = 0;
static uint32 PRGSIZE = 0, CHRSIZE = 0;

// Mapper registers.
static uint16 highBanks[8], lowBanks[2], chrBanks[16];
static uint8 fpgaRamBank, highMode, lowMode, chrMode, chrSource;
static uint8 ntBanks[4], ntControl[4];

// Scanline IRQ.
static uint8 slIrqEnabled, slIrqPending, slIrqScanline, slIrqOffset;
static int32 slIrqLastDot; // dot position at the previous check
static int32 slBaseLine; // PPU scanline where the scanline counter is 0, -1 when not in frame
static int32 renderOffDot; // dot position where rendering was disabled, -1 when enabled
static writefunc old2001Wr;
static uint32 frameStartTs; // CPU timestamp of scanline 0, dot 0
static uint32 frameStartValid;
static uint32 jitterBaseTs;

// CPU cycle IRQ.
static uint16 cpuIrqCounter, cpuIrqReloadValue;
static uint8 cpuIrqEnabled, cpuIrqPending, cpuIrqEnableAfterAck, cpuIrqAckOn4011;

// FPGA-RAM auto read/write.
static uint16 fpgaRamAddr;
static uint8 fpgaRamInc;

// Vector redirection.
static uint8 nmiVectorEnabled, irqVectorEnabled;
static uint16 nmiVectorAddr, irqVectorAddr;

// Audio (VRC6 like, read back through $4011).
struct RNBWPulse {
	uint8 volume, duty, ignoreDuty, enabled, step;
	uint16 freq;
	int32 timer;
};
struct RNBWSaw {
	uint8 rate, acc, enabled, step;
	uint16 freq;
	int32 timer;
};
static RNBWPulse pulse[2];
static RNBWSaw saw;
static uint8 audioCtrl, audioVolume, audioLastOutput;

static SFORMAT StateRegs[] =
{
	{ highBanks, sizeof(highBanks), "HBNK" },
	{ lowBanks, sizeof(lowBanks), "LBNK" },
	{ chrBanks, sizeof(chrBanks), "CBNK" },
	{ &fpgaRamBank, 1, "FBNK" },
	{ &highMode, 1, "HMOD" },
	{ &lowMode, 1, "LMOD" },
	{ &chrMode, 1, "CMOD" },
	{ &chrSource, 1, "CSRC" },
	{ ntBanks, 4, "NBNK" },
	{ ntControl, 4, "NCTL" },
	{ &RNBWHackBGBankOffset, 1, "BGOF" },
	{ &RNBWHackFillTile, 1, "FLTL" },
	{ &RNBWHackFillAttr, 1, "FLAT" },
	{ &slIrqEnabled, 1, "SIEN" },
	{ &slIrqPending, 1, "SIPD" },
	{ &slIrqScanline, 1, "SISL" },
	{ &slIrqOffset, 1, "SIOF" },
	{ &cpuIrqCounter, 2 | FCEUSTATE_RLSB, "CICN" },
	{ &cpuIrqReloadValue, 2 | FCEUSTATE_RLSB, "CIRL" },
	{ &cpuIrqEnabled, 1, "CIEN" },
	{ &cpuIrqPending, 1, "CIPD" },
	{ &cpuIrqEnableAfterAck, 1, "CIEA" },
	{ &cpuIrqAckOn4011, 1, "CIAK" },
	{ &fpgaRamAddr, 2 | FCEUSTATE_RLSB, "FRAD" },
	{ &fpgaRamInc, 1, "FRIN" },
	{ &nmiVectorEnabled, 1, "NVEN" },
	{ &irqVectorEnabled, 1, "IVEN" },
	{ &nmiVectorAddr, 2 | FCEUSTATE_RLSB, "NVAD" },
	{ &irqVectorAddr, 2 | FCEUSTATE_RLSB, "IVAD" },
	{ pulse, sizeof(pulse), "APUL" },
	{ &saw, sizeof(saw), "ASAW" },
	{ &audioCtrl, 1, "ACTL" },
	{ &audioVolume, 1, "AVOL" },
	{ &audioLastOutput, 1, "AOUT" },
	{ 0 }
};

static void UpdateIRQ(void) {
	if ((cpuIrqEnabled && cpuIrqPending) || (slIrqEnabled && slIrqPending))
		X6502_IRQBegin(FCEU_IQEXT);
	else
		X6502_IRQEnd(FCEU_IQEXT);
}

static uint8 *GetChrChip(uint32 *size) {
	switch (chrSource) {
	case 0:
		if (CHRSIZE) { *size = CHRSIZE; return VROM; }
		break;
	case 1:
		if (CHRRAMSIZE) { *size = CHRRAMSIZE; return CHRRAM; }
		break;
	}
	*size = FPGA_RAMSIZE;
	return FPGA_RAM;
}

static void SelectHighBank(uint32 A, uint32 size, int reg) {
	uint16 bank = highBanks[reg];
	int chip = (bank & 0x8000) ? 0x10 : 0;
	if (chip && !WRAM) chip = 0;
	bank &= 0x7FFF;
	switch (size) {
	case 0x8000: setprg32r(chip, A, bank); break;
	case 0x4000: setprg16r(chip, A, bank); break;
	case 0x2000: setprg8r(chip, A, bank); break;
	default:     setprg4r(chip, A, bank); break;
	}
}

static void SelectLowBank(uint32 A, uint32 size, int reg) {
	uint16 bank = lowBanks[reg];
	int chip;
	switch (bank >> 14) {
	case 2:  chip = WRAM ? 0x10 : 0x12; bank &= 0x3FFF; break;
	case 3:  chip = 0x12; bank &= 0x3FFF; break;
	default: chip = 0; bank &= 0x7FFF; break;
	}
	if (size == 0x2000)
		setprg8r(chip, A, bank);
	else
		setprg4r(chip, A, bank);
}

static void Sync(void) {
	int i;

	FCEUPPU_LineUpdate();

	// $8000-$FFFF
	switch (highMode) {
	case 0:
		SelectHighBank(0x8000, 0x8000, 0);
		break;
	case 1:
		SelectHighBank(0x8000, 0x4000, 0);
		SelectHighBank(0xC000, 0x4000, 4);
		break;
	case 2:
		SelectHighBank(0x8000, 0x4000, 0);
		SelectHighBank(0xC000, 0x2000, 4);
		SelectHighBank(0xE000, 0x2000, 6);
		break;
	case 3:
		for (i = 0; i < 4; i++)
			SelectHighBank(0x8000 + i * 0x2000, 0x2000, i * 2);
		break;
	default:
		for (i = 0; i < 8; i++)
			SelectHighBank(0x8000 + i * 0x1000, 0x1000, i);
		break;
	}

	// $6000-$7FFF
	if (lowMode) {
		SelectLowBank(0x6000, 0x1000, 0);
		SelectLowBank(0x7000, 0x1000, 1);
	} else {
		SelectLowBank(0x6000, 0x2000, 0);
	}

	// $5000-$5FFF, $4800-$4FFF
	setprg4r(0x12, 0x5000, fpgaRamBank);
	setprg2r(0x12, 0x4800, 3);

	// CHR, with 512 byte granularity for the renderer.
	{
		uint32 size;
		uint8 *chip = GetChrChip(&size);
		int writable = (chip != VROM);
		if (chrSource >= 2) {
			for (i = 0; i < 16; i++)
				RNBWHackVPage[i] = FPGA_RAM + ((i << 9) & 0xFFF) - (i << 9);
		} else {
			int mode = chrMode > 4 ? 4 : chrMode;
			int count = 1 << mode;
			uint32 bankSize = 0x2000 >> mode;
			int pagesPerBank = bankSize >> 9;
			for (i = 0; i < count; i++) {
				uint32 offs = ((uint32)chrBanks[i] * bankSize) & (size - 1);
				for (int p = 0; p < pagesPerBank; p++) {
					int page = i * pagesPerBank + p;
					RNBWHackVPage[page] = chip + offs + (p << 9) - (page << 9);
				}
			}
		}
		// VPage has 1K granularity: map the first 512 bytes of each 1K page
		// exactly, which is correct for every mode except the 512B one.
		for (i = 0; i < 8; i++)
			VPageR[i] = RNBWHackVPage[i << 1];
		PPUCHRRAM = writable ? 0xFF : 0;
		RNBWHackVROMPtr = chip;
		RNBWHackVROMMask = size - 1;
	}

	// Nametables.
	PPUNTARAM = 0;
	for (i = 0; i < 4; i++) {
		uint8 src = ntControl[i] >> 6;
		RNBWHackNTcontrol[i] = ntControl[i];
		if (src == 1 && !CHRRAMSIZE) src = 0;
		if (src == 3 && !CHRSIZE) src = 0;
		switch (src) {
		case 0: vnapage[i] = NTARAM + 0x400 * (ntBanks[i] & 1); PPUNTARAM |= 1 << i; break;
		case 1: vnapage[i] = CHRRAM + ((0x400 * ntBanks[i]) & (CHRRAMSIZE - 1)); PPUNTARAM |= 1 << i; break;
		case 2: vnapage[i] = FPGA_RAM + 0x400 * (ntBanks[i] & 3); PPUNTARAM |= 1 << i; break;
		case 3: vnapage[i] = VROM + ((0x400 * ntBanks[i]) & (CHRSIZE - 1)); break;
		}
	}
}

// ---------------------------------------------------------------------------
// Audio

static void AudioClock(void) {
	int i;
	for (i = 0; i < 2; i++) {
		RNBWPulse &p = pulse[i];
		if (p.enabled && --p.timer <= 0) {
			p.step = (p.step + 1) & 0x0F;
			p.timer = p.freq + 1;
		}
	}
	if (saw.enabled && --saw.timer <= 0) {
		saw.step = (saw.step + 1) % 14;
		saw.timer = saw.freq + 1;
		if (saw.step == 0)
			saw.acc = 0;
		else if (!(saw.step & 1))
			saw.acc += saw.rate;
	}
	uint8 out = 0;
	for (i = 0; i < 2; i++) {
		RNBWPulse &p = pulse[i];
		if (p.enabled && (p.ignoreDuty || p.step <= p.duty))
			out += p.volume;
	}
	if (saw.enabled)
		out += saw.acc >> 3;
	audioLastOutput = out;
}

static void AudioWrite(uint32 A, uint8 V) {
	switch (A) {
	case 0x41A0: case 0x41A3: {
		RNBWPulse &p = pulse[A == 0x41A3];
		p.volume = V & 0x0F;
		p.duty = (V & 0x70) >> 4;
		p.ignoreDuty = (V & 0x80) != 0;
		break;
	}
	case 0x41A1: case 0x41A4: {
		RNBWPulse &p = pulse[A == 0x41A4];
		p.freq = (p.freq & 0x0F00) | V;
		break;
	}
	case 0x41A2: case 0x41A5: {
		RNBWPulse &p = pulse[A == 0x41A5];
		p.freq = (p.freq & 0xFF) | ((V & 0x0F) << 8);
		p.enabled = (V & 0x80) != 0;
		if (!p.enabled) p.step = 0;
		break;
	}
	case 0x41A6: saw.rate = V & 0x3F; break;
	case 0x41A7: saw.freq = (saw.freq & 0x0F00) | V; break;
	case 0x41A8:
		saw.freq = (saw.freq & 0xFF) | ((V & 0x0F) << 8);
		saw.enabled = (V & 0x80) != 0;
		if (!saw.enabled) {
			saw.acc = 0;
			saw.step = 0;
		}
		break;
	case 0x41A9: audioCtrl = V & 0x07; break;
	case 0x41AA: audioVolume = V & 0x0F; break;
	}
}

// ---------------------------------------------------------------------------
// Scanline IRQ timing
//
// The old PPU renders a scanline at a time, so the scanline/dot position is
// derived from the CPU timestamp relative to the start of scanline 0.
// Mesen2 counts PPU reads from the start of the scanline (one read every two
// dots, starting at dot 1), so the IRQ fires at dot (2 * offset + 1).
//
// The hardware detects scanlines from PPU reads: when rendering is disabled
// the counter leaves the frame, and it restarts from 0 on the first scanline
// after rendering is enabled again. Games rely on this for splits following
// a forced blank.

static int32 CurrentDot(void) {
	if (!frameStartValid) return -1;
	int32 cycles = (int32)(timestamp - frameStartTs);
	if (cycles < 0) return -1;
	return PAL ? (cycles * 16 / 5) : (cycles * 3);
}


static void RainbowFrameStart(void) {
	frameStartTs = timestamp;
	frameStartValid = 1;
	slIrqLastDot = -1;
	slBaseLine = PPUON ? 0 : -1;
	renderOffDot = -1;
}

static DECLFW(RNBW_2001Wr) {
	uint8 wasOn = PPUON;
	old2001Wr(A, V);
	int32 dot = CurrentDot();
	if (dot < 0)
		return;
	if (wasOn && !PPUON) {
		renderOffDot = dot;
	} else if (!wasOn && PPUON) {
		// The in-frame flag is cleared after 3 CPU cycles without PPU reads.
		if (renderOffDot < 0 || dot - renderOffDot >= 9 || slBaseLine < 0) {
			int32 line = dot / 341;
			slBaseLine = line + ((dot % 341) < 337 ? 1 : 2);
		}
		renderOffDot = -1;
	}
}

static void CheckScanlineIRQ(void) {
	int32 dot = CurrentDot();
	int32 lastDot = slIrqLastDot;
	slIrqLastDot = dot;
	if (dot < 0 || slBaseLine < 0 || slBaseLine + slIrqScanline >= 240 || !PPUON)
		return;
	// Fire when the target position is crossed, so that the latch can be
	// rewritten for the next split within the same frame.
	int32 target = (slBaseLine + slIrqScanline) * 341 + slIrqOffset * 2 + 1;
	if (lastDot < target && dot >= target) {
		if (!slIrqPending) {
			slIrqPending = 1;
			if (slIrqEnabled && !(cpuIrqEnabled && cpuIrqPending)) {
				// Jitter counter starts when the IRQ line is asserted.
				int32 lateCycles = (dot - target) / 3;
				jitterBaseTs = timestamp - lateCycles;
			}
			UpdateIRQ();
		}
	}
}

static void RainbowIRQHook(int a) {
	for (int i = 0; i < a; i++) {
		AudioClock();
		if (cpuIrqCounter && --cpuIrqCounter == 0) {
			cpuIrqCounter = cpuIrqReloadValue;
			if (!cpuIrqPending) {
				cpuIrqPending = 1;
				if (cpuIrqEnabled && !(slIrqEnabled && slIrqPending))
					jitterBaseTs = timestamp - (a - 1 - i);
				UpdateIRQ();
			}
		}
	}
	CheckScanlineIRQ();
}

static void AckCpuIrq(void) {
	cpuIrqEnabled = cpuIrqEnableAfterAck;
	if (cpuIrqEnabled)
		cpuIrqCounter = cpuIrqReloadValue;
	cpuIrqPending = 0;
	UpdateIRQ();
}

// ---------------------------------------------------------------------------
// Register access

static DECLFR(RNBW_4011Rd) {
	if (cpuIrqAckOn4011)
		AckCpuIrq();
	return audioLastOutput << 1;
}

static DECLFR(RNBW_RegRd) {
	switch (A) {
	case 0x4100: return highMode | (lowMode << 7);
	case 0x4120: return chrMode | (chrSource << 6);
	case 0x412A: case 0x412B: case 0x412C: case 0x412D:
		return ntControl[A - 0x412A];
	case 0x4151: {
		int32 dot = CurrentDot();
		uint8 inFrame = 0, inHBlank = 0;
		if (PPUON && slBaseLine >= 0 && dot >= slBaseLine * 341 + 1 && dot < 240 * 341) {
			int32 lineDot = dot % 341;
			inFrame = 1;
			inHBlank = lineDot >= 257 || lineDot < 1;
		}
		uint8 ret = (inHBlank << 7) | (inFrame << 6) | slIrqPending;
		slIrqPending = 0;
		UpdateIRQ();
		return ret;
	}
	case 0x4154:
		return (uint8)(timestamp - jitterBaseTs);
	case 0x415F: {
		uint8 ret = FPGA_RAM[fpgaRamAddr];
		fpgaRamAddr = (fpgaRamAddr + fpgaRamInc) & 0x1FFF;
		return ret;
	}
	case 0x4160: return 0x20;
	case 0x4161: return (cpuIrqPending << 6) | (slIrqPending << 7);
	case 0x4190: case 0x4191: case 0x4192: return 0;
	}
	return X.DB;
}

static DECLFW(RNBW_RegWr) {
	if (A >= 0x4106 && A <= 0x4107) {
		lowBanks[A - 0x4106] = (lowBanks[A - 0x4106] & 0x00FF) | (V << 8);
		Sync();
	} else if (A >= 0x4116 && A <= 0x4117) {
		lowBanks[A - 0x4116] = (lowBanks[A - 0x4116] & 0xFF00) | V;
		Sync();
	} else if (A >= 0x4108 && A <= 0x410F) {
		highBanks[A - 0x4108] = (highBanks[A - 0x4108] & 0x00FF) | (V << 8);
		Sync();
	} else if (A >= 0x4118 && A <= 0x411F) {
		highBanks[A - 0x4118] = (highBanks[A - 0x4118] & 0xFF00) | V;
		Sync();
	} else if (A >= 0x4130 && A <= 0x413F) {
		chrBanks[A - 0x4130] = (chrBanks[A - 0x4130] & 0x00FF) | (V << 8);
		Sync();
	} else if (A >= 0x4140 && A <= 0x414F) {
		chrBanks[A - 0x4140] = (chrBanks[A - 0x4140] & 0xFF00) | V;
		Sync();
	} else if (A >= 0x4126 && A <= 0x4129) {
		ntBanks[A - 0x4126] = V;
		Sync();
	} else if (A >= 0x412A && A <= 0x412D) {
		ntControl[A - 0x412A] = V;
		Sync();
	} else if (A >= 0x41A0 && A <= 0x41AA) {
		AudioWrite(A, V);
	}

	switch (A) {
	case 0x4100:
		highMode = V & 0x07;
		lowMode = V >> 7;
		Sync();
		break;
	case 0x4115:
		fpgaRamBank = V & 0x01;
		Sync();
		break;
	case 0x4120:
		chrMode = V & 0x07;
		chrSource = V >> 6;
		Sync();
		break;
	case 0x4121:
		FCEUPPU_LineUpdate();
		RNBWHackBGBankOffset = V & 0x1F;
		break;
	case 0x4124:
		FCEUPPU_LineUpdate();
		RNBWHackFillTile = V;
		break;
	case 0x4125:
		FCEUPPU_LineUpdate();
		RNBWHackFillAttr = V & 0x03;
		break;
	case 0x4150: slIrqScanline = V; break;
	case 0x4151: slIrqEnabled = 1; UpdateIRQ(); break;
	case 0x4152:
		slIrqEnabled = 0;
		slIrqPending = 0;
		UpdateIRQ();
		break;
	case 0x4153: slIrqOffset = V < 1 ? 1 : (V > 170 ? 170 : V); break;
	case 0x4158: cpuIrqReloadValue = (cpuIrqReloadValue & 0x00FF) | (V << 8); break;
	case 0x4159: cpuIrqReloadValue = (cpuIrqReloadValue & 0xFF00) | V; break;
	case 0x415A:
		cpuIrqEnabled = V & 0x01;
		cpuIrqEnableAfterAck = (V & 0x02) != 0;
		cpuIrqAckOn4011 = (V & 0x04) != 0;
		if (cpuIrqEnabled)
			cpuIrqCounter = cpuIrqReloadValue;
		UpdateIRQ();
		break;
	case 0x415B: AckCpuIrq(); break;
	case 0x415C: fpgaRamAddr = (fpgaRamAddr & 0x00FF) | ((V & 0x1F) << 8); break;
	case 0x415D: fpgaRamAddr = (fpgaRamAddr & 0xFF00) | V; break;
	case 0x415E: fpgaRamInc = V; break;
	case 0x415F:
		FPGA_RAM[fpgaRamAddr] = V;
		fpgaRamAddr = (fpgaRamAddr + fpgaRamInc) & 0x1FFF;
		break;
	case 0x416B:
		nmiVectorEnabled = V & 0x01;
		irqVectorEnabled = (V & 0x02) != 0;
		break;
	case 0x416C: nmiVectorAddr = (nmiVectorAddr & 0x00FF) | (V << 8); break;
	case 0x416D: nmiVectorAddr = (nmiVectorAddr & 0xFF00) | V; break;
	case 0x416E: irqVectorAddr = (irqVectorAddr & 0x00FF) | (V << 8); break;
	case 0x416F: irqVectorAddr = (irqVectorAddr & 0xFF00) | V; break;
	}
}

static DECLFR(RNBW_VectorRd) {
	switch (A) {
	case 0xFFFA:
	case 0xFFFB:
		// NMI: the mapper leaves the frame and clears the scanline IRQ.
		slIrqPending = 0;
		UpdateIRQ();
		if (nmiVectorEnabled)
			return (A & 1) ? (nmiVectorAddr >> 8) : (nmiVectorAddr & 0xFF);
		break;
	case 0xFFFE:
	case 0xFFFF:
		if (irqVectorEnabled)
			return (A & 1) ? (irqVectorAddr >> 8) : (irqVectorAddr & 0xFF);
		break;
	}
	return CartBR(A);
}

// ---------------------------------------------------------------------------

static void RainbowReset(void) {
	memset(highBanks, 0, sizeof(highBanks));
	memset(lowBanks, 0, sizeof(lowBanks));
	memset(chrBanks, 0, sizeof(chrBanks));
	highMode = lowMode = chrMode = chrSource = fpgaRamBank = 0;
	ntBanks[0] = 0; ntBanks[1] = 0; ntBanks[2] = 1; ntBanks[3] = 1;
	memset(ntControl, 0, sizeof(ntControl));
	RNBWHackBGBankOffset = RNBWHackFillTile = RNBWHackFillAttr = 0;

	slIrqEnabled = slIrqPending = 0;
	slIrqLastDot = -1;
	slBaseLine = renderOffDot = -1;
	slIrqScanline = 0;
	slIrqOffset = 0x87;
	frameStartValid = 0;

	cpuIrqEnabled = cpuIrqPending = cpuIrqEnableAfterAck = cpuIrqAckOn4011 = 0;
	cpuIrqCounter = 0;
	nmiVectorEnabled = irqVectorEnabled = 0;

	memset(pulse, 0, sizeof(pulse));
	memset(&saw, 0, sizeof(saw));
	pulse[0].timer = pulse[1].timer = saw.timer = 1;
	audioCtrl = 0x03;
	audioVolume = 0x0F;
	audioLastOutput = 0;

	X6502_IRQEnd(FCEU_IQEXT);
	Sync();
}

static void RainbowPower(void) {
	RainbowReset();

	SetReadHandler(0x4100, 0x47FF, RNBW_RegRd);
	SetWriteHandler(0x4100, 0x47FF, RNBW_RegWr);
	SetReadHandler(0x4011, 0x4011, RNBW_4011Rd);
	SetReadHandler(0x4800, 0xFFFF, CartBR);
	SetWriteHandler(0x4800, 0xFFFF, CartBW);
	SetReadHandler(0xFFFA, 0xFFFF, RNBW_VectorRd);
	old2001Wr = GetWriteHandler(0x2001);
	for (uint32 a = 0x2001; a < 0x4000; a += 8)
		SetWriteHandler(a, a, RNBW_2001Wr);

	memset(FPGA_RAM, 0, FPGA_RAMSIZE);
	if (CHRRAM)
		memset(CHRRAM, 0, CHRRAMSIZE);
}

static void RainbowClose(void) {
	if (WRAM) FCEU_gfree(WRAM);
	if (FPGA_RAM) FCEU_gfree(FPGA_RAM);
	if (CHRRAM) FCEU_gfree(CHRRAM);
	WRAM = FPGA_RAM = CHRRAM = NULL;
	RNBWHack = 0;
	RNBWHackFrameStart = NULL;
}

static void StateRestore(int version) {
	frameStartValid = 0;
	Sync();
}

void RAINBOW_Init(CartInfo *info) {
	info->Power = RainbowPower;
	info->Reset = RainbowReset;
	info->Close = RainbowClose;
	GameStateRestore = StateRestore;
	MapIRQHook = RainbowIRQHook;

	PRGSIZE = ROM_size * 0x4000;
	CHRSIZE = VROM_size * 0x2000;

	WRAMSIZE = info->wram_size + info->battery_wram_size;
	if (!info->ines2) WRAMSIZE = 0x8000;
	if (WRAMSIZE) {
		if (WRAMSIZE < 0x2000) WRAMSIZE = 0x2000;
		WRAM = (uint8*)FCEU_gmalloc(WRAMSIZE);
		SetupCartPRGMapping(0x10, WRAM, WRAMSIZE, 1);
		AddExState(WRAM, WRAMSIZE, 0, "WRAM");
		if (info->battery) {
			info->SaveGame[0] = WRAM;
			info->SaveGameLen[0] = info->battery_wram_size ? info->battery_wram_size : WRAMSIZE;
		}
	}

	FPGA_RAM = (uint8*)FCEU_gmalloc(FPGA_RAMSIZE);
	SetupCartPRGMapping(0x12, FPGA_RAM, FPGA_RAMSIZE, 1);
	AddExState(FPGA_RAM, FPGA_RAMSIZE, 0, "FPGA");

	CHRRAMSIZE = info->vram_size + info->battery_vram_size;
	if (CHRRAMSIZE) {
		CHRRAM = (uint8*)FCEU_gmalloc(CHRRAMSIZE);
		AddExState(CHRRAM, CHRRAMSIZE, 0, "CRAM");
	}

	RNBWHack = 1;
	RNBWHackExNTARAMPtr = FPGA_RAM;
	RNBWHackFrameStart = RainbowFrameStart;

	AddExState(StateRegs, ~0, 0, 0);
}
