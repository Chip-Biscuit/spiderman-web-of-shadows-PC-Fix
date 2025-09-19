#pragma once
#include "stdafx.h"
#include <Windows.h>
#include <vector>

namespace mem
{
	void Patch(BYTE* dst, BYTE* src, unsigned int size);
	void Nop(BYTE* dst, unsigned int size);
	uintptr_t FindDMAAddy(uintptr_t ptr, std::vector<unsigned int> offsets);
	bool Hook(void* toHook, void* ourFunct, int len);
}