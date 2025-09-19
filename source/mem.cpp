#include "stdafx.h"
#include "mem.h"

void mem::Patch(BYTE* dst, BYTE* src, unsigned int size) {
    DWORD oldProtect;
    VirtualProtect(dst, size, PAGE_EXECUTE_READWRITE, &oldProtect);
    memcpy(dst, src, size);
    VirtualProtect(dst, size, oldProtect, &oldProtect);
}

void mem::Nop(BYTE* dst, unsigned int size) {
    DWORD oldProtect;
    VirtualProtect(dst, size, PAGE_EXECUTE_READWRITE, &oldProtect);
    memset(dst, 0x90, size);
    VirtualProtect(dst, size, oldProtect, &oldProtect);
}


uintptr_t mem::FindDMAAddy(uintptr_t ptr, std::vector<unsigned int> offsets) {
    uintptr_t addr = ptr;

    for (unsigned int i = 0; i < offsets.size(); ++i) {
        if (addr == 0)  // Check before dereferencing
            return 0;
        addr = *(uintptr_t*)addr;
        if (addr == 0) // Check after dereferencing
            return 0;
        addr += offsets[i];
    }
    return addr;
}


bool mem::Hook(void* toHook, void* ourFunct, int len) {
    if (len < 5) {
        return false;
    }

    DWORD curProtection;
    VirtualProtect(toHook, len, PAGE_EXECUTE_READWRITE, &curProtection);

    memset(toHook, 0x90, len);

    DWORD relativeAddress = ((DWORD)ourFunct - (DWORD)toHook) - 5;

    *(BYTE*)toHook = 0xE9;
    *(DWORD*)((DWORD)toHook + 1) = relativeAddress;

    DWORD temp;
    VirtualProtect(toHook, len, curProtection, &temp);

    return true;
}