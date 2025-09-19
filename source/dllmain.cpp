/**
* Copyright (C) 2020 Elisha Riedlinger
*
* This software is  provided 'as-is', without any express  or implied  warranty. In no event will the
* authors be held liable for any damages arising from the use of this software.
* Permission  is granted  to anyone  to use  this software  for  any  purpose,  including  commercial
* applications, and to alter it and redistribute it freely, subject to the following restrictions:
*
*   1. The origin of this software must not be misrepresented; you must not claim that you  wrote the
*      original  software. If you use this  software  in a product, an  acknowledgment in the product
*      documentation would be appreciated but is not required.
*   2. Altered source versions must  be plainly  marked as such, and  must not be  misrepresented  as
*      being the original software.
*   3. This notice may not be removed or altered from any source distribution.
*/
// chips spiderman web of shadows patches added 


#include "d3d9.h"
#include "d3dx9.h"
#include "iathook.h"
#include "helpers.h"
#include "mem.h"//chip
#include <iostream>//chip
#include <windows.h> // chip 
#include <vector> // chip
#include <Psapi.h> // chip
#include <string> //chip
#include <sstream> //chip
#include <iomanip> //chip
// spider_fov_toggle.cpp
#include <cstdint>
#include <cstdio>
//globals for frame limiter 
// --- FPS toggle globals ---
#include <atomic>
#include <fstream>


#pragma comment(lib, "d3dx9.lib")
#pragma comment(lib, "winmm.lib") // needed for timeBeginPeriod()/timeEndPeriod()

// chip - adding macros
# define DX_PRINT(x) std::cout << x << std::endl;
# define DX_ERROR(x) std::cerr << x << std::endl;
#define DX_MBPRINT(x) MessageBox(NULL, x, "Message", MB_OK);
#define DX_MBERROR(x) MessageBox(NULL, x, "Error", MB_ICONERROR | MB_OK);


Direct3DShaderValidatorCreate9Proc m_pDirect3DShaderValidatorCreate9;
PSGPErrorProc m_pPSGPError;
PSGPSampleTextureProc m_pPSGPSampleTexture;
D3DPERF_BeginEventProc m_pD3DPERF_BeginEvent;
D3DPERF_EndEventProc m_pD3DPERF_EndEvent;
D3DPERF_GetStatusProc m_pD3DPERF_GetStatus;
D3DPERF_QueryRepeatFrameProc m_pD3DPERF_QueryRepeatFrame;
D3DPERF_SetMarkerProc m_pD3DPERF_SetMarker;
D3DPERF_SetOptionsProc m_pD3DPERF_SetOptions;
D3DPERF_SetRegionProc m_pD3DPERF_SetRegion;
DebugSetLevelProc m_pDebugSetLevel;
DebugSetMuteProc m_pDebugSetMute;
Direct3D9EnableMaximizedWindowedModeShimProc m_pDirect3D9EnableMaximizedWindowedModeShim;
Direct3DCreate9Proc m_pDirect3DCreate9;
Direct3DCreate9ExProc m_pDirect3DCreate9Ex;

HWND g_hFocusWindow = NULL;
HMODULE g_hWrapperModule = NULL;

HMODULE d3d9dll = NULL;

float g_ActiveForcedValue = 0.0f; // 0 = inactive
bool g_ForceEnabled = false;
bool bForceWindowedMode;
bool bUsePrimaryMonitor;
bool bCenterWindow;
bool bAlwaysOnTop;
bool bDoNotNotifyOnTaskSwitch;
bool bDisplayFPSCounter;
bool bEnableHooks;
bool bCaptureMouse;
float fFPSLimit;
int nFullScreenRefreshRateInHz;
int nForceWindowStyle;

char WinDir[MAX_PATH+1];

// List of registered window classes and procedures
// WORD classAtom, ULONG_PTR WndProcPtr
std::vector<std::pair<WORD,ULONG_PTR>> WndProcList;


static std::atomic<int> g_FPSLimitHz{ 60 }; // default 60Hz
static std::atomic<bool> g_FpsTogglePrev{ false };
constexpr int FPS_TOGGLE_KEY = VK_F11; // change to any VK_* you prefer
// runtime configurable FPS toggle key (default F11)
static std::atomic<int>  g_fpsToggleKey{ VK_F11 };
static std::atomic<bool> g_fpsIsMouse{ false }; // true if VK_LBUTTON..VK_XBUTTON2
// ---------------------------
// Prototype so DllMain (and other early code) can call this before FrameLimiter is defined.
// mode: 2 == ACCURATE, otherwise == REALTIME
void ApplyFPSLimit(int hz, int mode);

//=======================================================================================================================================================================================

// chip - 2: NOP fov



// =================== Configuration example ===================
// d3d9.ini (place next to DLL/exe)
// [hotkey]
// ToggleKey=0x50        ; P
// RestoreKey=0x52       ; R
//
// OR your older style SpiderFov.ini
// [Hotkey]
// FOV_Toggle=0x50
// FOV_Restore=0x52
// =============================================================

namespace SpiderFov
{
    // -------- Configurable (FOV values still compile-time here) --------
    constexpr float FOV_VALUES[] = { 1.2f, 1.4f, 1.6f, 2.0f };
    constexpr size_t FOV_COUNT = sizeof(FOV_VALUES) / sizeof(FOV_VALUES[0]);

    // Re-apply interval in milliseconds.
    constexpr unsigned long long REAPPLY_INTERVAL_MS = 10000ULL; // 10s by default

    // Poll delay
    static std::atomic<DWORD> g_pollMs{ 75 };

    // If true, when the DLL unloads we'll attempt to restore the original FOV.
    constexpr bool RESTORE_ON_UNLOAD = true;

    // -------- Internal state (thread-safe where needed) --------
    static std::atomic<bool> g_threadRunning{ false };
    static HANDLE g_threadHandle = nullptr;
    static std::atomic<int> g_currentIndex{ -1 }; // -1 == none selected
    static std::atomic<bool> g_savedOriginalValid{ false };
    static float g_savedOriginal = 0.0f;
    static CRITICAL_SECTION g_savedCs; // protects g_savedOriginal when written/read

    // -------- Hotkey runtime configuration (set by SetCustomHotkey) --------
    static std::atomic<int> g_toggleKey{ VK_F9 };   // runtime toggle key
    static std::atomic<int> g_restoreKey{ VK_F10 }; // runtime restore key
    static std::atomic<bool> g_toggleIsMouse{ false };
    static std::atomic<bool> g_restoreIsMouse{ false };

    // -------- Helper: get module folder path (same as earlier versions) --------
    static std::string GetModuleFolderPath()
    {
        char buf[MAX_PATH];
        HMODULE hm = nullptr;
        if (!GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
            reinterpret_cast<LPCSTR>(&GetModuleFolderPath), &hm)) {
            hm = GetModuleHandleA(NULL);
        }
        if (!hm) return std::string();
        GetModuleFileNameA(hm, buf, MAX_PATH);
        std::string path(buf);
        size_t pos = path.find_last_of("\\/");
        if (pos != std::string::npos) path.resize(pos + 1);
        return path;
    }

    // -------- Simple trim + upper helpers --------
    static std::string Trim(const std::string& s) {
        size_t a = s.find_first_not_of(" \t\r\n");
        size_t b = s.find_last_not_of(" \t\r\n");
        return (a == std::string::npos) ? std::string() : s.substr(a, b - a + 1);
    }
    static std::string ToUpper(const std::string& s) {
        std::string out = s;
        std::transform(out.begin(), out.end(), out.begin(), [](unsigned char c) { return (char)std::toupper(c); });
        return out;
    }

    // -------- Read a single hotkey string from INI and parse to int (hex allowed) --------
    static int ReadHotkeyFromINI(const std::string& filePath, const char* section, const char* key, const char* def = "0x0")
    {
        char keyHex[64] = { 0 };
        GetPrivateProfileStringA(section, key, def, keyHex, (int)sizeof(keyHex), filePath.c_str());
        // strtol base 0 handles 0xNN hex and decimal
        long v = strtol(keyHex, nullptr, 0);
        return static_cast<int>(v);
    }

    // -------- Safe memory helpers (internal / static) --------
    static bool SafeReadPointerInternal(uintptr_t address, uintptr_t* out)
    {
        if (address == 0 || !out) return false;
        __try {
            *out = *reinterpret_cast<uintptr_t*>(address);
            return true;
        }
        __except (EXCEPTION_EXECUTE_HANDLER) {
            return false;
        }
    }

    static bool SafeReadFloatInternal(uintptr_t address, float* out)
    {
        if (address == 0 || !out) return false;
        __try {
            *out = *reinterpret_cast<float*>(address);
            return true;
        }
        __except (EXCEPTION_EXECUTE_HANDLER) {
            return false;
        }
    }

    static bool SafeWriteFloatInternal(uintptr_t address, float value)
    {
        if (address == 0) return false;
        __try {
            *reinterpret_cast<float*>(address) = value;
            return true;
        }
        __except (EXCEPTION_EXECUTE_HANDLER) {
            return false;
        }
    }

    // -------- Pointer chain resolver (internal) --------
    static uintptr_t ResolveSpiderManPointerInternal()
    {
        HMODULE mod = GetModuleHandleA("Spider-Man Web of Shadows.exe");
        if (!mod) return 0;
        uintptr_t moduleBase = reinterpret_cast<uintptr_t>(mod);

        uintptr_t basePointerAddr = moduleBase + 0x00BD3EA4;
        uintptr_t currentPtr = 0;
        if (!SafeReadPointerInternal(basePointerAddr, &currentPtr)) return 0;
        if (currentPtr == 0) return 0;

        const unsigned int offsets[] = { 0x10, 0x0, 0x2C, 0x1D8, 0x4, 0x1C0 };
        for (unsigned int off : offsets)
        {
            uintptr_t next = 0;
            if (!SafeReadPointerInternal(currentPtr + off, &next)) return 0;
            if (next == 0) return 0;
            currentPtr = next;
        }
        return currentPtr + 0x190; // final float offset
    }

    // -------- Helpers to save/restore original (thread-safe) --------
    static void SaveOriginalIfNeeded(uintptr_t finalAddr)
    {
        if (g_savedOriginalValid.load(std::memory_order_acquire)) return;

        float orig = 0.0f;
        if (!SafeReadFloatInternal(finalAddr, &orig)) return;

        EnterCriticalSection(&g_savedCs);
        g_savedOriginal = orig;
        g_savedOriginalValid.store(true, std::memory_order_release);
        LeaveCriticalSection(&g_savedCs);
    }

    static bool RestoreOriginalImmediate()
    {
        if (!g_savedOriginalValid.load(std::memory_order_acquire)) return false;
        uintptr_t finalAddr = ResolveSpiderManPointerInternal();
        if (!finalAddr) return 0;

        float orig;
        EnterCriticalSection(&g_savedCs);
        orig = g_savedOriginal;
        LeaveCriticalSection(&g_savedCs);

        if (!SafeWriteFloatInternal(finalAddr, orig)) return false;

        g_currentIndex.store(-1, std::memory_order_relaxed);
        return true;
    }

    // -------- Write/read helpers that use resolver --------
    static bool WriteFovByIndexImmediate(size_t idx)
    {
        if (idx >= FOV_COUNT) return false;
        uintptr_t finalAddr = ResolveSpiderManPointerInternal();
        if (!finalAddr) return false;

        // save original once
        SaveOriginalIfNeeded(finalAddr);

        float target = FOV_VALUES[idx];
        return SafeWriteFloatInternal(finalAddr, target);
    }

    // -------- Set custom hotkeys (reads d3d9.ini or fallback to SpiderFov.ini) --------
    static void SetCustomHotkey()
    {
        // determine folder & ini paths
        std::string folder = GetModuleFolderPath();
        std::string d3d9path = folder + "d3d9.ini";
        std::string spiderPath = folder + "SpiderFov.ini";

        // First try d3d9.ini [hotkey] ToggleKey / RestoreKey
        std::ifstream f(d3d9path);
        if (f.good()) {
            f.close();
            int t = ReadHotkeyFromINI(d3d9path, "hotkey", "ToggleKey", "0");
            int r = ReadHotkeyFromINI(d3d9path, "hotkey", "RestoreKey", "0");
            // fallback try capitalized section if missing
            if (t == 0 && r == 0) {
                t = ReadHotkeyFromINI(d3d9path, "Hotkey", "ToggleKey", "0");
                r = ReadHotkeyFromINI(d3d9path, "Hotkey", "RestoreKey", "0");
            }
            if (t != 0) g_toggleKey.store(t);
            if (r != 0) g_restoreKey.store(r);
        }
        else {
            // fallback: read old-style keys from SpiderFov.ini section [Hotkey] FOV_Toggle / FOV_Restore
            std::ifstream f2(spiderPath);
            if (f2.good()) {
                f2.close();
                int t2 = ReadHotkeyFromINI(spiderPath, "Hotkey", "FOV_Toggle", "0");
                int r2 = ReadHotkeyFromINI(spiderPath, "Hotkey", "FOV_Restore", "0");
                if (t2 != 0) g_toggleKey.store(t2);
                if (r2 != 0) g_restoreKey.store(r2);
            }
        }

        // detect if toggle/restore are mouse buttons (VK_LBUTTON..VK_XBUTTON2)
        int tk = g_toggleKey.load();
        int rk = g_restoreKey.load();
        g_toggleIsMouse.store(tk >= VK_LBUTTON && tk <= VK_XBUTTON2);
        g_restoreIsMouse.store(rk >= VK_LBUTTON && rk <= VK_XBUTTON2);

        // intentionally no messagebox / debug output
    }

    // -------- Thread proc (handles hotkey + periodic reapply + restore hotkey) --------
    static DWORD WINAPI ToggleThreadProc(LPVOID)
    {
        bool prevTogglePressed = false;
        bool prevRestorePressed = false;
        unsigned long long lastWriteTs = 0ULL;

        g_currentIndex.store(-1);

        while (g_threadRunning.load(std::memory_order_relaxed))
        {
            int toggleKey = g_toggleKey.load(std::memory_order_relaxed);
            int restoreKey = g_restoreKey.load(std::memory_order_relaxed);
            DWORD poll = g_pollMs.load();

            // GetAsyncKeyState works for mouse VKs (0x01..0x06) too
            SHORT stT = toggleKey ? GetAsyncKeyState(toggleKey) : 0;
            bool togglePressed = (stT & 0x8000) != 0;
            if (togglePressed && !prevTogglePressed)
            {
                int cur = g_currentIndex.load(std::memory_order_relaxed);
                cur = (cur + 1) % static_cast<int>(FOV_COUNT);
                g_currentIndex.store(cur, std::memory_order_relaxed);

                if (WriteFovByIndexImmediate(static_cast<size_t>(cur)))
                {
                    lastWriteTs = GetTickCount64();
                }
            }
            prevTogglePressed = togglePressed;

            SHORT stR = restoreKey ? GetAsyncKeyState(restoreKey) : 0;
            bool restorePressed = (stR & 0x8000) != 0;
            if (restorePressed && !prevRestorePressed)
            {
                RestoreOriginalImmediate();
            }
            prevRestorePressed = restorePressed;

            // Periodic reapply if an index is active
            int activeIdx = g_currentIndex.load(std::memory_order_relaxed);
            if (activeIdx >= 0)
            {
                unsigned long long now = GetTickCount64();
                if (lastWriteTs == 0ULL || (now - lastWriteTs) >= REAPPLY_INTERVAL_MS)
                {
                    if (WriteFovByIndexImmediate(static_cast<size_t>(activeIdx)))
                    {
                        lastWriteTs = now;
                    }
                }
            }

            Sleep(poll);
        }

        // restore on shutdown if desired
        if (RESTORE_ON_UNLOAD) {
            RestoreOriginalImmediate();
        }

        return 0;
    }

    // -------- Public start/stop (also init/destroy CS) --------
    void StartToggleThread()
    {
        if (g_threadRunning.load()) return;

        // set hotkeys now (reads INI but NO confirmation)
        SetCustomHotkey();

        InitializeCriticalSection(&g_savedCs);
        g_savedOriginalValid.store(false);
        g_savedOriginal = 0.0f;
        g_currentIndex.store(-1);

        g_threadRunning.store(true);
        g_threadHandle = CreateThread(nullptr, 0, ToggleThreadProc, nullptr, 0, nullptr);
        if (!g_threadHandle) {
            g_threadRunning.store(false);
            DeleteCriticalSection(&g_savedCs);
        }
    }

    void StopToggleThread()
    {
        if (!g_threadRunning.load()) return;
        g_threadRunning.store(false);
        if (g_threadHandle) {
            WaitForSingleObject(g_threadHandle, 2000);
            CloseHandle(g_threadHandle);
            g_threadHandle = nullptr;
        }
        DeleteCriticalSection(&g_savedCs);
    }

} // namespace SpiderFov




//=========================================================================================================================================================================================================
//chip
// Function to perform the hex edit
void PerformHexEdit(LPBYTE lpAddress, DWORD moduleSize) {
    // Define the patterns to search for and their corresponding new values
    struct HexEdit {
        std::vector<BYTE> pattern;
        std::vector<BYTE> newValue;
        size_t offset; // Offset of the byte to modify within the pattern
    };

    // Define the edits
    std::vector<HexEdit> edits = {
        
        { { 0xF3, 0x0F, 0x11, 0x86, 0x90, 0x01, 0x00, 0x00, 0x5E, 0x83, 0xC4, 0x20, 0xC2, 0x04, 0x00, 0xCC,
0xCC, 0xCC, 0xCC, 0x56, 0x8B, 0xF1, 0x8B, 0x86, 0x3C, 0x01, 0x00, 0x00, 0x83, 0xF8, 0x01, 0x74 }, { 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x5E, 0x83, 0xC4, 0x20, 0xC2, 0x04, 0x00, 0xCC,
0xCC, 0xCC, 0xCC, 0x56, 0x8B, 0xF1, 0x8B, 0x86, 0x3C, 0x01, 0x00, 0x00, 0x83, 0xF8, 0x01, 0x74 }, 0 },
    };

    // Iterate through the edits
    for (const auto& edit : edits) {
        // Search for the pattern in memory
        for (DWORD i = 0; i < moduleSize - edit.pattern.size(); ++i) {
            if (memcmp(lpAddress + i, edit.pattern.data(), edit.pattern.size()) == 0) {
                // Pattern found in memory
                std::cout << "Pattern found in memory." << std::endl;

                // Modify memory
                LPVOID lpAddressToWrite = lpAddress + i + edit.offset;
                SIZE_T numberOfBytesWritten;
                BOOL result = WriteProcessMemory(GetCurrentProcess(), lpAddressToWrite, edit.newValue.data(), edit.newValue.size(), &numberOfBytesWritten);
                if (!result || numberOfBytesWritten != edit.newValue.size()) {
                    std::cerr << "Failed to write memory." << std::endl;
                    return;
                }
                std::cout << "Hex edited successfully." << std::endl;
                break;
            }
        }
    }
}

// Function to perform the hex edits
void PerformHexEdits() {
    // Get the handle to the current module
    HMODULE hModule = GetModuleHandle(NULL);
    if (hModule == NULL) {
        std::cerr << "Failed to get module handle." << std::endl;
        return;
    }

    // Get the module information
    LPBYTE lpAddress = reinterpret_cast<LPBYTE>(hModule);
    DWORD moduleSize = 0; // Placeholder for module size
    TCHAR szFileName[MAX_PATH];
    if (GetModuleFileNameEx(GetCurrentProcess(), hModule, szFileName, MAX_PATH)) {
        moduleSize = GetFileSize(szFileName, NULL);
    }
    if (moduleSize == 0) {
        std::cerr << "Failed to get module information." << std::endl;
        return;
    }

    // Perform the hex edit
    PerformHexEdit(lpAddress, moduleSize);
}
//chip
//=========================================================================================================================================================================================================


void HookModule(HMODULE hmod);
LRESULT WINAPI CustomWndProcA(HWND hWnd, UINT uMsg, WPARAM wParam, LPARAM lParam);
LRESULT WINAPI CustomWndProcW(HWND hWnd, UINT uMsg, WPARAM wParam, LPARAM lParam);

class FrameLimiter
{
private:
    static inline double TIME_Frequency = 0.0;
    static inline double TIME_Ticks = 0.0;
    static inline double TIME_Frametime = 0.0;

public:
    static inline ID3DXFont* pFPSFont = nullptr;
    static inline ID3DXFont* pTimeFont = nullptr;

public:
    enum FPSLimitMode { FPS_NONE, FPS_REALTIME, FPS_ACCURATE };
    static void Init(FPSLimitMode mode)
    {
        LARGE_INTEGER frequency;

        QueryPerformanceFrequency(&frequency);
        static constexpr auto TICKS_PER_FRAME = 1;
        auto TICKS_PER_SECOND = (TICKS_PER_FRAME * fFPSLimit);
        if (mode == FPS_ACCURATE)
        {
            TIME_Frametime = 1000.0 / (double)fFPSLimit;
            TIME_Frequency = (double)frequency.QuadPart / 1000.0; // ticks are milliseconds
        }
        else // FPS_REALTIME
        {
            TIME_Frequency = (double)frequency.QuadPart / (double)TICKS_PER_SECOND; // ticks are 1/n frames (n = fFPSLimit)
        }
        Ticks();
    }
    static DWORD Sync_RT()
    {
        DWORD lastTicks, currentTicks;
        LARGE_INTEGER counter;

        QueryPerformanceCounter(&counter);
        lastTicks = (DWORD)TIME_Ticks;
        TIME_Ticks = (double)counter.QuadPart / TIME_Frequency;
        currentTicks = (DWORD)TIME_Ticks;

        return (currentTicks > lastTicks) ? currentTicks - lastTicks : 0;
    }
    static DWORD Sync_SLP()
    {
        LARGE_INTEGER counter;
        QueryPerformanceCounter(&counter);
        double millis_current = (double)counter.QuadPart / TIME_Frequency;
        double millis_delta = millis_current - TIME_Ticks;
        if (TIME_Frametime <= millis_delta)
        {
            TIME_Ticks = millis_current;
            return 1;
        }
        else if (TIME_Frametime - millis_delta > 2.0) // > 2ms
            Sleep(1); // Sleep for ~1ms
        else
            Sleep(0); // yield thread's time-slice (does not actually sleep)

        return 0;
    }
    static void ShowFPS(LPDIRECT3DDEVICE9EX device)
    {
        static std::list<int> m_times;

        //https://github.com/microsoft/VCSamples/blob/master/VC2012Samples/Windows%208%20samples/C%2B%2B/Windows%208%20app%20samples/Direct2D%20geometry%20realization%20sample%20(Windows%208)/C%2B%2B/FPSCounter.cpp#L279
        LARGE_INTEGER frequency;
        LARGE_INTEGER time;
        QueryPerformanceFrequency(&frequency);
        QueryPerformanceCounter(&time);

        if (m_times.size() == 50)
            m_times.pop_front();
        m_times.push_back(static_cast<int>(time.QuadPart));

        uint32_t fps = 0;
        if (m_times.size() >= 2)
            fps = static_cast<uint32_t>(0.5f + (static_cast<float>(m_times.size() - 1) * static_cast<float>(frequency.QuadPart)) / static_cast<float>(m_times.back() - m_times.front()));

        static int space = 0;
        if (!pFPSFont || !pTimeFont)
        {
            D3DDEVICE_CREATION_PARAMETERS cparams;
            RECT rect;
            device->GetCreationParameters(&cparams);
            GetClientRect(cparams.hFocusWindow, &rect);

            D3DXFONT_DESC fps_font;
            ZeroMemory(&fps_font, sizeof(D3DXFONT_DESC));
            fps_font.Height = rect.bottom / 20;
            fps_font.Width = 0;
            fps_font.Weight = 400;
            fps_font.MipLevels = 0;
            fps_font.Italic = 0;
            fps_font.CharSet = DEFAULT_CHARSET;
            fps_font.OutputPrecision = OUT_DEFAULT_PRECIS;
            fps_font.Quality = ANTIALIASED_QUALITY;
            fps_font.PitchAndFamily = DEFAULT_PITCH | FF_DONTCARE;
            wchar_t FaceName[] = L"Arial";
            memcpy(&fps_font.FaceName, &FaceName, sizeof(FaceName));

            D3DXFONT_DESC time_font = fps_font;
            time_font.Height = rect.bottom / 35;
            space = fps_font.Height + 5;

            if (D3DXCreateFontIndirect(device, &fps_font, &pFPSFont) != D3D_OK)
                return;

            if (D3DXCreateFontIndirect(device, &time_font, &pTimeFont) != D3D_OK)
                return;
        }
        else
        {
            auto DrawTextOutline = [](ID3DXFont* pFont, FLOAT X, FLOAT Y, D3DXCOLOR dColor, CONST PCHAR cString, ...)
            {
                const D3DXCOLOR BLACK(D3DCOLOR_XRGB(0, 0, 0));
                CHAR cBuffer[101] = "";

                va_list oArgs;
                va_start(oArgs, cString);
                _vsnprintf((cBuffer + strlen(cBuffer)), (sizeof(cBuffer) - strlen(cBuffer)), cString, oArgs);
                va_end(oArgs);

                RECT Rect[5] =
                {
                    { X - 1, Y, X + 500.0f, Y + 50.0f },
                    { X, Y - 1, X + 500.0f, Y + 50.0f },
                    { X + 1, Y, X + 500.0f, Y + 50.0f },
                    { X, Y + 1, X + 500.0f, Y + 50.0f },
                    { X, Y, X + 500.0f, Y + 50.0f },
                };

                if (dColor != BLACK)
                {
                    for (auto i = 0; i < 4; i++)
                        pFont->DrawText(NULL, cBuffer, -1, &Rect[i], DT_NOCLIP, BLACK);
                }

                pFont->DrawText(NULL, cBuffer, -1, &Rect[4], DT_NOCLIP, dColor);
            };

            static char str_format_fps[] = "%02d";
            static char str_format_time[] = "%.01f ms";
            static const D3DXCOLOR YELLOW(D3DCOLOR_XRGB(0xF7, 0xF7, 0));
            DrawTextOutline(pFPSFont, 10, 10, YELLOW, str_format_fps, fps);
            DrawTextOutline(pTimeFont, 10, space, YELLOW, str_format_time, (1.0f / fps) * 1000.0f);
        }
    }

private:
    static void Ticks()
    {
        LARGE_INTEGER counter;
        QueryPerformanceCounter(&counter);
        TIME_Ticks = (double)counter.QuadPart / TIME_Frequency;
    }
};

FrameLimiter::FPSLimitMode mFPSLimitMode = FrameLimiter::FPSLimitMode::FPS_NONE;

HRESULT m_IDirect3DDevice9Ex::Present(CONST RECT* pSourceRect, CONST RECT* pDestRect, HWND hDestWindowOverride, CONST RGNDATA* pDirtyRegion)
{
    if (mFPSLimitMode == FrameLimiter::FPSLimitMode::FPS_REALTIME)
        while (!FrameLimiter::Sync_RT());
    else if (mFPSLimitMode == FrameLimiter::FPSLimitMode::FPS_ACCURATE)
        while (!FrameLimiter::Sync_SLP());

    return ProxyInterface->Present(pSourceRect, pDestRect, hDestWindowOverride, pDirtyRegion);
}

HRESULT m_IDirect3DDevice9Ex::PresentEx(THIS_ CONST RECT* pSourceRect, CONST RECT* pDestRect, HWND hDestWindowOverride, CONST RGNDATA* pDirtyRegion, DWORD dwFlags)
{
    if (mFPSLimitMode == FrameLimiter::FPSLimitMode::FPS_REALTIME)
        while (!FrameLimiter::Sync_RT());
    else if (mFPSLimitMode == FrameLimiter::FPSLimitMode::FPS_ACCURATE)
        while (!FrameLimiter::Sync_SLP());

    return ProxyInterface->PresentEx(pSourceRect, pDestRect, hDestWindowOverride, pDirtyRegion, dwFlags);
}

// actual implementation: placed after FrameLimiter and after the mFPSLimitMode declaration
void ApplyFPSLimit(int hz, int mode)
{
    // convert int mode into the FrameLimiter enum
    FrameLimiter::FPSLimitMode newMode = (mode == 2) ? FrameLimiter::FPSLimitMode::FPS_ACCURATE : FrameLimiter::FPSLimitMode::FPS_REALTIME;

    // handle switching timer resolution when entering/exiting ACCURATE mode
    if (mFPSLimitMode == FrameLimiter::FPSLimitMode::FPS_ACCURATE && newMode != FrameLimiter::FPSLimitMode::FPS_ACCURATE)
    {
        timeEndPeriod(1);
    }
    if (newMode == FrameLimiter::FPSLimitMode::FPS_ACCURATE && mFPSLimitMode != FrameLimiter::FPSLimitMode::FPS_ACCURATE)
    {
        timeBeginPeriod(1);
    }

    if (hz <= 0)
    {
        fFPSLimit = 0.0f;
        mFPSLimitMode = FrameLimiter::FPSLimitMode::FPS_NONE;
    }
    else
    {
        fFPSLimit = static_cast<float>(hz);
        // Re-init FrameLimiter with the new mode
        FrameLimiter::Init(newMode);
        mFPSLimitMode = newMode;
    }

    // store numeric limit for toggle UI / detection
    g_FPSLimitHz.store((hz <= 0) ? 0 : hz);

   
}


HRESULT m_IDirect3DDevice9Ex::EndScene()
{
    if (bDisplayFPSCounter)
        FrameLimiter::ShowFPS(ProxyInterface);

    // FPS toggle 60 <=> 30 (edge-detect on key press)
    {
        bool pressed = (GetAsyncKeyState(g_fpsToggleKey.load()) & 0x8000) != 0;
        bool prev = g_FpsTogglePrev.load();
        if (pressed && !prev) // key down edge
        {
            int cur = g_FPSLimitHz.load();
            int next = (cur == 60) ? 30 : 60;
            g_FPSLimitHz.store(next);
            // Re-apply using current mode (mFPSLimitMode) so accurate/realtime choice stays
            int modeAsInt = (int)mFPSLimitMode;
            if (modeAsInt == (int)FrameLimiter::FPSLimitMode::FPS_NONE)
                modeAsInt = 1; // default to REALTIME
            ApplyFPSLimit(next, modeAsInt);

           
        }
        g_FpsTogglePrev.store(pressed);
    }


    return ProxyInterface->EndScene();
}

void CaptureMouse(HWND hWnd)
{
    RECT window_rect;
    GetWindowRect(hWnd, &window_rect);
    if (window_rect.left < 0)
        window_rect.left = 0;
    if (window_rect.top < 0)
        window_rect.top = 0;
    SetCapture(hWnd);
    ClipCursor(&window_rect);
}

void ForceWindowed(D3DPRESENT_PARAMETERS* pPresentationParameters, D3DDISPLAYMODEEX* pFullscreenDisplayMode = NULL)
{
    HWND hwnd = pPresentationParameters->hDeviceWindow ? pPresentationParameters->hDeviceWindow : g_hFocusWindow;
    HMONITOR monitor = MonitorFromWindow((!bUsePrimaryMonitor && hwnd) ? hwnd : GetDesktopWindow(), MONITOR_DEFAULTTONEAREST);
    MONITORINFO info;
    info.cbSize = sizeof(MONITORINFO);
    GetMonitorInfo(monitor, &info);
    int DesktopResX = info.rcMonitor.right - info.rcMonitor.left;
    int DesktopResY = info.rcMonitor.bottom - info.rcMonitor.top;

    int left = (int)info.rcMonitor.left;
    int top = (int)info.rcMonitor.top;

    if (nForceWindowStyle != 1) // not borderless fullscreen
    {
        left += (int)(((float)DesktopResX / 2.0f) - ((float)pPresentationParameters->BackBufferWidth / 2.0f));
        top += (int)(((float)DesktopResY / 2.0f) - ((float)pPresentationParameters->BackBufferHeight / 2.0f));
    }

    pPresentationParameters->Windowed = 1;

    // This must be set to default (0) on windowed mode as per D3D9 spec
    pPresentationParameters->FullScreen_RefreshRateInHz = D3DPRESENT_RATE_DEFAULT;

    // If exists, this must match the rate in PresentationParameters
    if (pFullscreenDisplayMode != NULL)
        pFullscreenDisplayMode->RefreshRate = D3DPRESENT_RATE_DEFAULT;

    // This flag is not available on windowed mode as per D3D9 spec
    pPresentationParameters->PresentationInterval &= ~D3DPRESENT_DONOTFLIP;

    if (hwnd != NULL)
    {
        int cx, cy;
        UINT uFlags = SWP_SHOWWINDOW;
        LONG lOldStyle = GetWindowLong(hwnd, GWL_STYLE);
        LONG lOldExStyle = GetWindowLong(hwnd, GWL_EXSTYLE);
        LONG lNewStyle, lNewExStyle;

        lOldExStyle &= ~(WS_EX_TOPMOST);

        if (nForceWindowStyle == 1)
        {
            cx = DesktopResX;
            cy = DesktopResY;
        }
        else
        {
            cx = pPresentationParameters->BackBufferWidth;
            cy = pPresentationParameters->BackBufferHeight;

            if (!bCenterWindow)
                uFlags |= SWP_NOMOVE;
        }

        switch(nForceWindowStyle)
        {
            case 1: // borderless fullscreen
            case 4: // borderless window (no style)
                lNewStyle = lOldStyle & ~(WS_CAPTION | WS_THICKFRAME | WS_MINIMIZE | WS_MAXIMIZE | WS_SYSMENU | WS_MINIMIZEBOX | WS_MAXIMIZEBOX | WS_DLGFRAME);
                lNewStyle |= (lOldStyle & WS_CHILD) ? 0 : WS_POPUP;
                lNewExStyle = lOldExStyle & ~(WS_EX_CONTEXTHELP | WS_EX_DLGMODALFRAME | WS_EX_CLIENTEDGE | WS_EX_STATICEDGE | WS_EX_WINDOWEDGE | WS_EX_TOOLWINDOW);
                lNewExStyle |= WS_EX_APPWINDOW;
                break;
            case 2: // window
                lNewStyle = (WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX);
                lNewExStyle = (WS_EX_APPWINDOW | WS_EX_WINDOWEDGE | WS_EX_CLIENTEDGE);
                break;
            case 3: // resizable window
                lNewStyle = (WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX | WS_THICKFRAME | WS_MAXIMIZEBOX);
                lNewExStyle = (WS_EX_APPWINDOW | WS_EX_WINDOWEDGE | WS_EX_CLIENTEDGE);
                break;
        }

        if (nForceWindowStyle)
        {
            if (lNewStyle != lOldStyle)
            {
                SetWindowLong(hwnd, GWL_STYLE, lNewStyle);
                uFlags |= SWP_FRAMECHANGED;
            }
            if (lNewExStyle != lOldExStyle)
            {
                SetWindowLong(hwnd, GWL_EXSTYLE, lNewExStyle);
                uFlags |= SWP_FRAMECHANGED;
            }
        }
        SetWindowPos(hwnd, bAlwaysOnTop ? HWND_TOPMOST : HWND_NOTOPMOST, left, top, cx, cy, uFlags);

        if (bDoNotNotifyOnTaskSwitch || bCaptureMouse)
        {
            if (bCaptureMouse)
                CaptureMouse(hwnd);

            WORD wClassAtom = GetClassWord(hwnd, GCW_ATOM);
            if (wClassAtom != 0)
            {
                bool found = false;
                for (unsigned int i = 0; i < WndProcList.size(); i++) {
                    if (WndProcList[i].first == wClassAtom) {
                        found = true;
                        break;
                    }
                }
                if (!found)
                {
                    LONG_PTR wndproc = GetWindowLongPtr(hwnd, GWLP_WNDPROC);
                    WndProcList.emplace_back(wClassAtom, wndproc);
                    SetWindowLongPtr(hwnd, GWLP_WNDPROC, IsWindowUnicode(hwnd) ? (LONG_PTR)CustomWndProcW : (LONG_PTR)CustomWndProcA);
                }
            }
        }
    }
}

void ForceFullScreenRefreshRateInHz(D3DPRESENT_PARAMETERS* pPresentationParameters)
{
    if (!pPresentationParameters->Windowed)
    {
        std::vector<int> list;
        DISPLAY_DEVICE dd;
        dd.cb = sizeof(DISPLAY_DEVICE);
        DWORD deviceNum = 0;
        while (EnumDisplayDevices(NULL, deviceNum, &dd, 0))
        {
            DISPLAY_DEVICE newdd = { 0 };
            newdd.cb = sizeof(DISPLAY_DEVICE);
            DWORD monitorNum = 0;
            DEVMODE dm = { 0 };
            while (EnumDisplayDevices(dd.DeviceName, monitorNum, &newdd, 0))
            {
                for (auto iModeNum = 0; EnumDisplaySettings(NULL, iModeNum, &dm) != 0; iModeNum++)
                    list.emplace_back(dm.dmDisplayFrequency);
                monitorNum++;
            }
            deviceNum++;
        }

        std::sort(list.begin(), list.end());
        if (nFullScreenRefreshRateInHz > list.back() || nFullScreenRefreshRateInHz < list.front() || nFullScreenRefreshRateInHz < 0)
            pPresentationParameters->FullScreen_RefreshRateInHz = list.back();
        else
            pPresentationParameters->FullScreen_RefreshRateInHz = nFullScreenRefreshRateInHz;
    }
}

HRESULT m_IDirect3D9Ex::CreateDevice(UINT Adapter, D3DDEVTYPE DeviceType, HWND hFocusWindow, DWORD BehaviorFlags, D3DPRESENT_PARAMETERS* pPresentationParameters, IDirect3DDevice9** ppReturnedDeviceInterface)
{
    g_hFocusWindow = hFocusWindow ? hFocusWindow : pPresentationParameters->hDeviceWindow;
    if (bForceWindowedMode)
    {
        ForceWindowed(pPresentationParameters);
    }

    if (nFullScreenRefreshRateInHz)
        ForceFullScreenRefreshRateInHz(pPresentationParameters);

    if (bDisplayFPSCounter)
    {
        if (FrameLimiter::pFPSFont)
            FrameLimiter::pFPSFont->Release();
        if (FrameLimiter::pTimeFont)
            FrameLimiter::pTimeFont->Release();
        FrameLimiter::pFPSFont = nullptr;
        FrameLimiter::pTimeFont = nullptr;
    }

    HRESULT hr = ProxyInterface->CreateDevice(Adapter, DeviceType, hFocusWindow, BehaviorFlags, pPresentationParameters, ppReturnedDeviceInterface);

    if (SUCCEEDED(hr) && ppReturnedDeviceInterface)
    {
        *ppReturnedDeviceInterface = new m_IDirect3DDevice9Ex((IDirect3DDevice9Ex*)*ppReturnedDeviceInterface, this, IID_IDirect3DDevice9);
    }

    return hr;
}

HRESULT m_IDirect3DDevice9Ex::Reset(D3DPRESENT_PARAMETERS* pPresentationParameters)
{
    if (bForceWindowedMode)
        ForceWindowed(pPresentationParameters);

    if (nFullScreenRefreshRateInHz)
        ForceFullScreenRefreshRateInHz(pPresentationParameters);

    if (bDisplayFPSCounter)
    {
        if (FrameLimiter::pFPSFont)
            FrameLimiter::pFPSFont->OnLostDevice();
        if (FrameLimiter::pTimeFont)
            FrameLimiter::pTimeFont->OnLostDevice();
    }

    auto hRet = ProxyInterface->Reset(pPresentationParameters);

    if (bDisplayFPSCounter)
    {
        if (SUCCEEDED(hRet))
        {
            if (FrameLimiter::pFPSFont)
                FrameLimiter::pFPSFont->OnResetDevice();
            if (FrameLimiter::pTimeFont)
                FrameLimiter::pTimeFont->OnResetDevice();
        }
    }

    return hRet;
}

HRESULT m_IDirect3D9Ex::CreateDeviceEx(THIS_ UINT Adapter, D3DDEVTYPE DeviceType, HWND hFocusWindow, DWORD BehaviorFlags, D3DPRESENT_PARAMETERS* pPresentationParameters, D3DDISPLAYMODEEX* pFullscreenDisplayMode, IDirect3DDevice9Ex** ppReturnedDeviceInterface)
{
    g_hFocusWindow = hFocusWindow ? hFocusWindow : pPresentationParameters->hDeviceWindow;
    if (bForceWindowedMode)
    {
        ForceWindowed(pPresentationParameters, pFullscreenDisplayMode);
    }

    if (nFullScreenRefreshRateInHz)
        ForceFullScreenRefreshRateInHz(pPresentationParameters);

    if (bDisplayFPSCounter)
    {
        if (FrameLimiter::pFPSFont)
            FrameLimiter::pFPSFont->Release();
        if (FrameLimiter::pTimeFont)
            FrameLimiter::pTimeFont->Release();
        FrameLimiter::pFPSFont = nullptr;
        FrameLimiter::pTimeFont = nullptr;
    }

    HRESULT hr = ProxyInterface->CreateDeviceEx(Adapter, DeviceType, hFocusWindow, BehaviorFlags, pPresentationParameters, pFullscreenDisplayMode, ppReturnedDeviceInterface);

    if (SUCCEEDED(hr) && ppReturnedDeviceInterface)
    {
        *ppReturnedDeviceInterface = new m_IDirect3DDevice9Ex(*ppReturnedDeviceInterface, this, IID_IDirect3DDevice9Ex);
    }

    return hr;
}

HRESULT m_IDirect3DDevice9Ex::ResetEx(THIS_ D3DPRESENT_PARAMETERS* pPresentationParameters, D3DDISPLAYMODEEX* pFullscreenDisplayMode)
{
    if (bForceWindowedMode)
        ForceWindowed(pPresentationParameters, pFullscreenDisplayMode);

    if (nFullScreenRefreshRateInHz)
        ForceFullScreenRefreshRateInHz(pPresentationParameters);

    if (bDisplayFPSCounter)
    {
        if (FrameLimiter::pFPSFont)
            FrameLimiter::pFPSFont->OnLostDevice();
        if (FrameLimiter::pTimeFont)
            FrameLimiter::pTimeFont->OnLostDevice();
    }

    auto hRet = ProxyInterface->ResetEx(pPresentationParameters, pFullscreenDisplayMode);

    if (bDisplayFPSCounter)
    {
        if (SUCCEEDED(hRet))
        {
            if (FrameLimiter::pFPSFont)
                FrameLimiter::pFPSFont->OnResetDevice();
            if (FrameLimiter::pTimeFont)
                FrameLimiter::pTimeFont->OnResetDevice();
        }
    }

    return hRet;
}

LRESULT WINAPI CustomWndProc(HWND hWnd, UINT uMsg, WPARAM wParam, LPARAM lParam, int idx)
{
    if (hWnd == g_hFocusWindow || _fnIsTopLevelWindow(hWnd)) // skip child windows like buttons, edit boxes, etc.
    {
        if (bAlwaysOnTop)
        {
            if ((GetWindowLong(hWnd, GWL_EXSTYLE) & WS_EX_TOPMOST) == 0)
                SetWindowPos(hWnd, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOACTIVATE | SWP_NOMOVE | SWP_NOSIZE);
        }
        switch (uMsg)
        {
            case WM_ACTIVATE:
                if (bDoNotNotifyOnTaskSwitch && LOWORD(wParam) == WA_INACTIVE)
                {
                    if ((HWND)lParam == NULL)
                        return 0;
                    DWORD dwPID = 0;
                    GetWindowThreadProcessId((HWND)lParam, &dwPID);
                    if (dwPID != GetCurrentProcessId())
                        return 0;
                }
                if (bCaptureMouse && LOWORD(wParam) != WA_INACTIVE)
                    CaptureMouse(hWnd);
                break;
            case WM_NCACTIVATE:
                if (bDoNotNotifyOnTaskSwitch && LOWORD(wParam) == WA_INACTIVE)
                    return 0;
                if (bCaptureMouse && LOWORD(wParam) != WA_INACTIVE)
                    CaptureMouse(hWnd);
                break;
            case WM_ACTIVATEAPP:
                if (bDoNotNotifyOnTaskSwitch && wParam == FALSE)
                    return 0;
                if (bCaptureMouse && wParam == TRUE)
                    CaptureMouse(hWnd);
                break;
            case WM_KILLFOCUS:
                if (bDoNotNotifyOnTaskSwitch)
                {
                    if ((HWND)wParam == NULL)
                        return 0;
                    DWORD dwPID = 0;
                    GetWindowThreadProcessId((HWND)wParam, &dwPID);
                    if (dwPID != GetCurrentProcessId())
                        return 0;
                }
                break;
            case WM_SETFOCUS:
            case WM_MOUSEACTIVATE:
                if (bCaptureMouse)
                    CaptureMouse(hWnd);
                break;
            default:
                break;
        }
    }
    WNDPROC OrigProc = WNDPROC(WndProcList[idx].second);
    return OrigProc(hWnd, uMsg, wParam, lParam);
}

LRESULT WINAPI CustomWndProcA(HWND hWnd, UINT uMsg, WPARAM wParam, LPARAM lParam)
{
    WORD wClassAtom = GetClassWord(hWnd, GCW_ATOM);
    if (wClassAtom)
    {
        for (unsigned int i = 0; i < WndProcList.size(); i++) {
            if (WndProcList[i].first == wClassAtom) {
                return CustomWndProc(hWnd, uMsg, wParam, lParam, i);
            }
        }
    }
    // We should never reach here, but having safeguards anyway is good
    return DefWindowProcA(hWnd, uMsg, wParam, lParam);
}

LRESULT WINAPI CustomWndProcW(HWND hWnd, UINT uMsg, WPARAM wParam, LPARAM lParam)
{
    WORD wClassAtom = GetClassWord(hWnd, GCW_ATOM);
    if (wClassAtom)
    {
        for (unsigned int i = 0; i < WndProcList.size(); i++) {
            if (WndProcList[i].first == wClassAtom) {
                return CustomWndProc(hWnd, uMsg, wParam, lParam, i);
            }
        }
    }
    // We should never reach here, but having safeguards anyway is good
    return DefWindowProcW(hWnd, uMsg, wParam, lParam);
}

typedef ATOM(__stdcall* RegisterClassA_fn)(const WNDCLASSA*);
typedef ATOM(__stdcall* RegisterClassW_fn)(const WNDCLASSW*);
typedef ATOM(__stdcall* RegisterClassExA_fn)(const WNDCLASSEXA*);
typedef ATOM(__stdcall* RegisterClassExW_fn)(const WNDCLASSEXW*);
RegisterClassA_fn oRegisterClassA = NULL;
RegisterClassW_fn oRegisterClassW = NULL;
RegisterClassExA_fn oRegisterClassExA = NULL;
RegisterClassExW_fn oRegisterClassExW = NULL;
ATOM __stdcall hk_RegisterClassA(WNDCLASSA* lpWndClass)
{
    if (!IsValueIntAtom(DWORD(lpWndClass->lpszClassName))) { // argument is a class name
        if (IsSystemClassNameA(lpWndClass->lpszClassName)) { // skip system classes like buttons, common controls, etc.
            return oRegisterClassA(lpWndClass);
        }
    }
    ULONG_PTR pWndProc = ULONG_PTR(lpWndClass->lpfnWndProc);
    lpWndClass->lpfnWndProc = CustomWndProcA;
    WORD wClassAtom = oRegisterClassA(lpWndClass);
    if (wClassAtom != 0)
    {
        WndProcList.emplace_back(wClassAtom, pWndProc);
    }
    return wClassAtom;
}
ATOM __stdcall hk_RegisterClassW(WNDCLASSW* lpWndClass)
{
    if (!IsValueIntAtom(DWORD(lpWndClass->lpszClassName))) { // argument is a class name
        if (IsSystemClassNameW(lpWndClass->lpszClassName)) { // skip system classes like buttons, common controls, etc.
            return oRegisterClassW(lpWndClass);
        }
    }
    ULONG_PTR pWndProc = ULONG_PTR(lpWndClass->lpfnWndProc);
    lpWndClass->lpfnWndProc = CustomWndProcW;
    WORD wClassAtom = oRegisterClassW(lpWndClass);
    if (wClassAtom != 0)
    {
        WndProcList.emplace_back(wClassAtom, pWndProc);
    }
    return wClassAtom;
}
ATOM __stdcall hk_RegisterClassExA(WNDCLASSEXA* lpWndClass)
{
    if (!IsValueIntAtom(DWORD(lpWndClass->lpszClassName))) { // argument is a class name
        if (IsSystemClassNameA(lpWndClass->lpszClassName)) { // skip system classes like buttons, common controls, etc.
            return oRegisterClassExA(lpWndClass);
        }
    }
    ULONG_PTR pWndProc = ULONG_PTR(lpWndClass->lpfnWndProc);
    lpWndClass->lpfnWndProc = CustomWndProcA;
    WORD wClassAtom = oRegisterClassExA(lpWndClass);
    if (wClassAtom != 0)
    {
        WndProcList.emplace_back(wClassAtom, pWndProc);
    }
    return wClassAtom;
}
ATOM __stdcall hk_RegisterClassExW(WNDCLASSEXW* lpWndClass)
{
    if (!IsValueIntAtom(DWORD(lpWndClass->lpszClassName))) { // argument is a class name
        if (IsSystemClassNameW(lpWndClass->lpszClassName)) { // skip system classes like buttons, common controls, etc.
            return oRegisterClassExW(lpWndClass);
        }
    }
    ULONG_PTR pWndProc = ULONG_PTR(lpWndClass->lpfnWndProc);
    lpWndClass->lpfnWndProc = CustomWndProcW;
    WORD wClassAtom = oRegisterClassExW(lpWndClass);
    if (wClassAtom != 0)
    {
        WndProcList.emplace_back(wClassAtom, pWndProc);
    }
    return wClassAtom;
}

typedef HWND(__stdcall* GetForegroundWindow_fn)(void);
GetForegroundWindow_fn oGetForegroundWindow = NULL;

HWND __stdcall hk_GetForegroundWindow()
{
    if (g_hFocusWindow && IsWindow(g_hFocusWindow))
        return g_hFocusWindow;
    return oGetForegroundWindow();
}

typedef HWND(__stdcall* GetActiveWindow_fn)(void);
GetActiveWindow_fn oGetActiveWindow = NULL;

HWND __stdcall hk_GetActiveWindow(void)
{
    HWND hWndActive = oGetActiveWindow();
    if (g_hFocusWindow && hWndActive == NULL && IsWindow(g_hFocusWindow))
    {
        if (GetCurrentThreadId() == GetWindowThreadProcessId(g_hFocusWindow, NULL))
            return g_hFocusWindow;
    }
    return hWndActive;
}

typedef HWND(__stdcall* GetFocus_fn)(void);
GetFocus_fn oGetFocus = NULL;

HWND __stdcall hk_GetFocus(void)
{
    HWND hWndFocus = oGetFocus();
    if (g_hFocusWindow && hWndFocus == NULL && IsWindow(g_hFocusWindow))
    {
        if (GetCurrentThreadId() == GetWindowThreadProcessId(g_hFocusWindow, NULL))
            return g_hFocusWindow;
    }
    return hWndFocus;
}

typedef HMODULE(__stdcall* LoadLibraryA_fn)(LPCSTR lpLibFileName);
LoadLibraryA_fn oLoadLibraryA;

HMODULE __stdcall hk_LoadLibraryA(LPCSTR lpLibFileName)
{
    HMODULE hmod = oLoadLibraryA(lpLibFileName);
    if (hmod)
    {
        HookModule(hmod);
    }
    return hmod;
}

typedef HMODULE(__stdcall* LoadLibraryW_fn)(LPCWSTR lpLibFileName);
LoadLibraryW_fn oLoadLibraryW;

HMODULE __stdcall hk_LoadLibraryW(LPCWSTR lpLibFileName)
{
    HMODULE hmod = oLoadLibraryW(lpLibFileName);
    if (hmod)
    {
        HookModule(hmod);
    }
    return hmod;
}

typedef HMODULE(__stdcall* LoadLibraryExA_fn)(LPCSTR lpLibFileName, HANDLE hFile, DWORD dwFlags);
LoadLibraryExA_fn oLoadLibraryExA;

HMODULE __stdcall hk_LoadLibraryExA(LPCSTR lpLibFileName, HANDLE hFile, DWORD dwFlags)
{
    HMODULE hmod = oLoadLibraryExA(lpLibFileName, hFile, dwFlags);
    if (hmod && ((dwFlags & (LOAD_LIBRARY_AS_DATAFILE | LOAD_LIBRARY_AS_DATAFILE_EXCLUSIVE | LOAD_LIBRARY_AS_IMAGE_RESOURCE)) == 0))
    {
        HookModule(hmod);
    }
    return hmod;
}

typedef HMODULE(__stdcall* LoadLibraryExW_fn)(LPCWSTR lpLibFileName, HANDLE hFile, DWORD dwFlags);
LoadLibraryExW_fn oLoadLibraryExW;

HMODULE __stdcall hk_LoadLibraryExW(LPCWSTR lpLibFileName, HANDLE hFile, DWORD dwFlags)
{
    HMODULE hmod = oLoadLibraryExW(lpLibFileName, hFile, dwFlags);
    if (hmod && ((dwFlags & (LOAD_LIBRARY_AS_DATAFILE | LOAD_LIBRARY_AS_DATAFILE_EXCLUSIVE | LOAD_LIBRARY_AS_IMAGE_RESOURCE)) == 0))
    {
        HookModule(hmod);
    }
    return hmod;
}

typedef BOOL(__stdcall* FreeLibrary_fn)(HMODULE hLibModule);
FreeLibrary_fn oFreeLibrary;

BOOL __stdcall hk_FreeLibrary(HMODULE hLibModule)
{
    if (hLibModule == g_hWrapperModule)
        return TRUE; // We will stay in memory, thank you very much

    return oFreeLibrary(hLibModule);
}

FARPROC __stdcall hk_GetProcAddress(HMODULE hModule, LPCSTR lpProcName)
{
    __try
    {
        if (!lstrcmpA(lpProcName, "RegisterClassA"))
        {
            if (oRegisterClassA == NULL)
                oRegisterClassA = (RegisterClassA_fn)GetProcAddress(hModule, lpProcName);
            return (FARPROC)hk_RegisterClassA;
        }
        if (!lstrcmpA(lpProcName, "RegisterClassW"))
        {
            if (oRegisterClassW == NULL)
                oRegisterClassW = (RegisterClassW_fn)GetProcAddress(hModule, lpProcName);
            return (FARPROC)hk_RegisterClassW;
        }
        if (!lstrcmpA(lpProcName, "RegisterClassExA"))
        {
            if (oRegisterClassExA == NULL)
                oRegisterClassExA = (RegisterClassExA_fn)GetProcAddress(hModule, lpProcName);
            return (FARPROC)hk_RegisterClassExA;
        }
        if (!lstrcmpA(lpProcName, "RegisterClassExW"))
        {
            if (oRegisterClassExW == NULL)
                oRegisterClassExW = (RegisterClassExW_fn)GetProcAddress(hModule, lpProcName);
            return (FARPROC)hk_RegisterClassExW;
        }
        if (!lstrcmpA(lpProcName, "GetForegroundWindow"))
        {
            if (oGetForegroundWindow == NULL)
                oGetForegroundWindow = (GetForegroundWindow_fn)GetProcAddress(hModule, lpProcName);
            return (FARPROC)hk_GetForegroundWindow;
        }
        if (!lstrcmpA(lpProcName, "GetActiveWindow"))
        {
            if (oGetActiveWindow == NULL)
                oGetActiveWindow = (GetActiveWindow_fn)GetProcAddress(hModule, lpProcName);
            return (FARPROC)hk_GetActiveWindow;
        }
        if (!lstrcmpA(lpProcName, "GetFocus"))
        {
            if (oGetFocus == NULL)
                oGetFocus = (GetFocus_fn)GetProcAddress(hModule, lpProcName);
            return (FARPROC)hk_GetFocus;
        }
        if (!lstrcmpA(lpProcName, "LoadLibraryA"))
        {
            if (oLoadLibraryA == NULL)
                oLoadLibraryA = (LoadLibraryA_fn)GetProcAddress(hModule, lpProcName);
            return (FARPROC)hk_LoadLibraryA;
        }
        if (!lstrcmpA(lpProcName, "LoadLibraryW"))
        {
            if (oLoadLibraryW == NULL)
                oLoadLibraryW = (LoadLibraryW_fn)GetProcAddress(hModule, lpProcName);
            return (FARPROC)hk_LoadLibraryW;
        }
        if (!lstrcmpA(lpProcName, "LoadLibraryExA"))
        {
            if (oLoadLibraryExA == NULL)
                oLoadLibraryExA = (LoadLibraryExA_fn)GetProcAddress(hModule, lpProcName);
            return (FARPROC)hk_LoadLibraryExA;
        }
        if (!lstrcmpA(lpProcName, "LoadLibraryExW"))
        {
            if (oLoadLibraryExW == NULL)
                oLoadLibraryExW = (LoadLibraryExW_fn)GetProcAddress(hModule, lpProcName);
            return (FARPROC)hk_LoadLibraryExW;
        }
        if (!lstrcmpA(lpProcName, "FreeLibrary"))
        {
            if (oFreeLibrary == NULL)
                oFreeLibrary = (FreeLibrary_fn)GetProcAddress(hModule, lpProcName);
            return (FARPROC)hk_FreeLibrary;
        }
    }
    __except ((GetExceptionCode() == EXCEPTION_ACCESS_VIOLATION) ? EXCEPTION_EXECUTE_HANDLER : EXCEPTION_CONTINUE_SEARCH)
    {
    }

    return GetProcAddress(hModule, lpProcName);
}

void HookModule(HMODULE hmod)
{
    char modpath[MAX_PATH + 1];
    if (hmod == g_hWrapperModule) // Yeah, let's not go and hook ourselves
        return;
    if (GetModuleFileNameA(hmod, modpath, MAX_PATH)) {
        if (!_strnicmp(modpath, WinDir, strlen(WinDir))) { // skip system modules
            return;
        }
    }
    if (oRegisterClassA == NULL)
        oRegisterClassA = (RegisterClassA_fn)Iat_hook::detour_iat_ptr("RegisterClassA", (void*)hk_RegisterClassA, hmod);
    else
        Iat_hook::detour_iat_ptr("RegisterClassA", (void*)hk_RegisterClassA, hmod);

    if (oRegisterClassW == NULL)
        oRegisterClassW = (RegisterClassW_fn)Iat_hook::detour_iat_ptr("RegisterClassW", (void*)hk_RegisterClassW, hmod);
    else
        Iat_hook::detour_iat_ptr("RegisterClassW", (void*)hk_RegisterClassW, hmod);

    if (oRegisterClassExA == NULL)
        oRegisterClassExA = (RegisterClassExA_fn)Iat_hook::detour_iat_ptr("RegisterClassExA", (void*)hk_RegisterClassExA, hmod);
    else
        Iat_hook::detour_iat_ptr("RegisterClassExA", (void*)hk_RegisterClassExA, hmod);

    if (oRegisterClassExW == NULL)
        oRegisterClassExW = (RegisterClassExW_fn)Iat_hook::detour_iat_ptr("RegisterClassExW", (void*)hk_RegisterClassExW, hmod);
    else
        Iat_hook::detour_iat_ptr("RegisterClassExW", (void*)hk_RegisterClassExW, hmod);

    if (oGetForegroundWindow == NULL)
        oGetForegroundWindow = (GetForegroundWindow_fn)Iat_hook::detour_iat_ptr("GetForegroundWindow", (void*)hk_GetForegroundWindow, hmod);
    else
        Iat_hook::detour_iat_ptr("GetForegroundWindow", (void*)hk_GetForegroundWindow, hmod);

    if (oGetActiveWindow == NULL)
        oGetActiveWindow = (GetActiveWindow_fn)Iat_hook::detour_iat_ptr("GetActiveWindow", (void*)hk_GetActiveWindow, hmod);
    else
        Iat_hook::detour_iat_ptr("GetActiveWindow", (void*)hk_GetActiveWindow, hmod);

    if (oGetFocus == NULL)
        oGetFocus = (GetFocus_fn)Iat_hook::detour_iat_ptr("GetFocus", (void*)hk_GetFocus, hmod);
    else
        Iat_hook::detour_iat_ptr("GetFocus", (void*)hk_GetFocus, hmod);

    if (oLoadLibraryA == NULL)
        oLoadLibraryA = (LoadLibraryA_fn)Iat_hook::detour_iat_ptr("LoadLibraryA", (void*)hk_LoadLibraryA, hmod);
    else
        Iat_hook::detour_iat_ptr("LoadLibraryA", (void*)hk_LoadLibraryA, hmod);

    if (oLoadLibraryW == NULL)
        oLoadLibraryW = (LoadLibraryW_fn)Iat_hook::detour_iat_ptr("LoadLibraryW", (void*)hk_LoadLibraryW, hmod);
    else
        Iat_hook::detour_iat_ptr("LoadLibraryW", (void*)hk_LoadLibraryW, hmod);

    if (oLoadLibraryExA == NULL)
        oLoadLibraryExA = (LoadLibraryExA_fn)Iat_hook::detour_iat_ptr("LoadLibraryExA", (void*)hk_LoadLibraryExA, hmod);
    else
        Iat_hook::detour_iat_ptr("LoadLibraryExA", (void*)hk_LoadLibraryExA, hmod);

    if (oLoadLibraryExW == NULL)
        oLoadLibraryExW = (LoadLibraryExW_fn)Iat_hook::detour_iat_ptr("LoadLibraryExW", (void*)hk_LoadLibraryExW, hmod);
    else
        Iat_hook::detour_iat_ptr("LoadLibraryExW", (void*)hk_LoadLibraryExW, hmod);

    if (oFreeLibrary == NULL)
        oFreeLibrary = (FreeLibrary_fn)Iat_hook::detour_iat_ptr("FreeLibrary", (void*)hk_FreeLibrary, hmod);
    else
        Iat_hook::detour_iat_ptr("FreeLibrary", (void*)hk_FreeLibrary, hmod);

    Iat_hook::detour_iat_ptr("GetProcAddress", (void*)hk_GetProcAddress, hmod);
}

void HookImportedModules()
{
    HMODULE hModule;
    HMODULE hm;

    hModule = GetModuleHandle(0);

    PIMAGE_DOS_HEADER img_dos_headers = (PIMAGE_DOS_HEADER)hModule;
    PIMAGE_NT_HEADERS img_nt_headers = (PIMAGE_NT_HEADERS)((BYTE*)img_dos_headers + img_dos_headers->e_lfanew);
    PIMAGE_IMPORT_DESCRIPTOR img_import_desc = (PIMAGE_IMPORT_DESCRIPTOR)((BYTE*)img_dos_headers + img_nt_headers->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT].VirtualAddress);
    if (img_dos_headers->e_magic != IMAGE_DOS_SIGNATURE)
        return;

    for (IMAGE_IMPORT_DESCRIPTOR* iid = img_import_desc; iid->Name != 0; iid++) {
        char* mod_name = (char*)((size_t*)(iid->Name + (size_t)hModule));
        hm = GetModuleHandleA(mod_name);
        // ual check
        if (hm && !(GetProcAddress(hm, "DirectInput8Create") != NULL && GetProcAddress(hm, "DirectSoundCreate8") != NULL && GetProcAddress(hm, "InternetOpenA") != NULL)) {
            HookModule(hm);
        }
    }
}

bool WINAPI DllMain(HMODULE hModule, DWORD dwReason, LPVOID lpReserved)
{
    switch (dwReason)
    {
        case DLL_PROCESS_ATTACH:
        {
            g_hWrapperModule = hModule;

            // Load dll
            char path[MAX_PATH];
            GetSystemDirectoryA(path, MAX_PATH);
            strcat_s(path, "\\d3d9.dll");
            d3d9dll = LoadLibraryA(path);

            //========================================================================================================================
          //chip

            if (dwReason == DLL_PROCESS_ATTACH)
            {

                PerformHexEdits();

                SpiderFov::StartToggleThread();

            }

            //chip
            //========================================================================================================================

            if (d3d9dll)
            {
                // Get function addresses
                m_pDirect3DShaderValidatorCreate9 = (Direct3DShaderValidatorCreate9Proc)GetProcAddress(d3d9dll, "Direct3DShaderValidatorCreate9");
                m_pPSGPError = (PSGPErrorProc)GetProcAddress(d3d9dll, "PSGPError");
                m_pPSGPSampleTexture = (PSGPSampleTextureProc)GetProcAddress(d3d9dll, "PSGPSampleTexture");
                m_pD3DPERF_BeginEvent = (D3DPERF_BeginEventProc)GetProcAddress(d3d9dll, "D3DPERF_BeginEvent");
                m_pD3DPERF_EndEvent = (D3DPERF_EndEventProc)GetProcAddress(d3d9dll, "D3DPERF_EndEvent");
                m_pD3DPERF_GetStatus = (D3DPERF_GetStatusProc)GetProcAddress(d3d9dll, "D3DPERF_GetStatus");
                m_pD3DPERF_QueryRepeatFrame = (D3DPERF_QueryRepeatFrameProc)GetProcAddress(d3d9dll, "D3DPERF_QueryRepeatFrame");
                m_pD3DPERF_SetMarker = (D3DPERF_SetMarkerProc)GetProcAddress(d3d9dll, "D3DPERF_SetMarker");
                m_pD3DPERF_SetOptions = (D3DPERF_SetOptionsProc)GetProcAddress(d3d9dll, "D3DPERF_SetOptions");
                m_pD3DPERF_SetRegion = (D3DPERF_SetRegionProc)GetProcAddress(d3d9dll, "D3DPERF_SetRegion");
                m_pDebugSetLevel = (DebugSetLevelProc)GetProcAddress(d3d9dll, "DebugSetLevel");
                m_pDebugSetMute = (DebugSetMuteProc)GetProcAddress(d3d9dll, "DebugSetMute");
                m_pDirect3D9EnableMaximizedWindowedModeShim = (Direct3D9EnableMaximizedWindowedModeShimProc)GetProcAddress(d3d9dll, "Direct3D9EnableMaximizedWindowedModeShim");
                m_pDirect3DCreate9 = (Direct3DCreate9Proc)GetProcAddress(d3d9dll, "Direct3DCreate9");
                m_pDirect3DCreate9Ex = (Direct3DCreate9ExProc)GetProcAddress(d3d9dll, "Direct3DCreate9Ex");

                // ini
                HMODULE hm = NULL;
                GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT, (LPCSTR)&Direct3DCreate9, &hm);
                GetModuleFileNameA(hm, path, sizeof(path));
                strcpy(strrchr(path, '\\'), "\\d3d9.ini");
                bForceWindowedMode = GetPrivateProfileInt("MAIN", "ForceWindowedMode", 0, path) != 0;
               //FPSLimit = static_cast<float>(GetPrivateProfileInt("MAIN", "FPSLimit", 0, path));
                nFullScreenRefreshRateInHz = GetPrivateProfileInt("MAIN", "FullScreenRefreshRateInHz", 0, path);
                bDisplayFPSCounter = GetPrivateProfileInt("MAIN", "DisplayFPSCounter", 0, path);
                bEnableHooks = GetPrivateProfileInt("MAIN", "EnableHooks", 0, path);
                bUsePrimaryMonitor = GetPrivateProfileInt("FORCEWINDOWED", "UsePrimaryMonitor", 0, path) != 0;
                bCenterWindow = GetPrivateProfileInt("FORCEWINDOWED", "CenterWindow", 1, path) != 0;
                bAlwaysOnTop = GetPrivateProfileInt("FORCEWINDOWED", "AlwaysOnTop", 0, path) != 0;
                bDoNotNotifyOnTaskSwitch = GetPrivateProfileInt("FORCEWINDOWED", "DoNotNotifyOnTaskSwitch", 0, path) != 0;
                nForceWindowStyle = GetPrivateProfileInt("FORCEWINDOWED", "ForceWindowStyle", 0, path);
                bCaptureMouse = GetPrivateProfileInt("FORCEWINDOWED", "CaptureMouse", 0, path) != 0;

                // --- load FPS toggle hotkey (d3d9.ini [hotkey] FpsToggle OR SpiderFov.ini [Hotkey] FPS_Toggle) ---
                {
                    char keyBuf[64] = { 0 };
                    // try d3d9.ini [hotkey] FpsToggle first
                    GetPrivateProfileStringA("hotkey", "FpsToggle", "", keyBuf, (int)sizeof(keyBuf), path);
                    if (keyBuf[0] == '\0') {
                        // try capitalized section / older naming in d3d9.ini
                        GetPrivateProfileStringA("Hotkey", "FpsToggle", "", keyBuf, (int)sizeof(keyBuf), path);
                    }

                    if (keyBuf[0] == '\0') {
                        // fallback to old SpiderFov.ini naming (if you keep a SpiderFov.ini next to the DLL)
                        // spiderPath is same as 'path' here unless you use a different filename; if you wrote SpiderFov.ini elsewhere, adjust.
                        // Try "FPS_Toggle" which your older code used.
                        GetPrivateProfileStringA("Hotkey", "FPS_Toggle", "", keyBuf, (int)sizeof(keyBuf), path);
                    }

                    if (keyBuf[0] != '\0') {
                        long v = strtol(keyBuf, nullptr, 0); // base 0 -> accepts 0x.. hex or decimal
                        if (v != 0) {
                            g_fpsToggleKey.store((int)v);
                            g_fpsIsMouse.store(((int)v >= VK_LBUTTON && (int)v <= VK_XBUTTON2));
                        }
                    }
                    // if no valid entry found, g_fpsToggleKey remains VK_F11
                }

                int initModeInt = GetPrivateProfileInt("MAIN", "FPSLimitMode", 1, path); // 2 => ACCURATE, otherwise REALTIME

                // Set default 60 (ignore any FPSLimit read from INI)
                g_FPSLimitHz.store(60);
                ApplyFPSLimit(60, initModeInt);


                //if (fFPSLimit > 0.0f)
                //{
                  //  FrameLimiter::FPSLimitMode mode = (GetPrivateProfileInt("MAIN", "FPSLimitMode", 1, path) == 2) ? FrameLimiter::FPSLimitMode::FPS_ACCURATE : FrameLimiter::FPSLimitMode::FPS_REALTIME;
                    //if (mode == FrameLimiter::FPSLimitMode::FPS_ACCURATE)
                      //  timeBeginPeriod(1);
                //
                  //  FrameLimiter::Init(mode);
                    //mFPSLimitMode = mode;
                //}
                //else
                  //  mFPSLimitMode = FrameLimiter::FPSLimitMode::FPS_NONE;

                if (bEnableHooks && (bDoNotNotifyOnTaskSwitch || bCaptureMouse))
                {
                    GetSystemWindowsDirectoryA(WinDir, MAX_PATH);

                    oRegisterClassA = (RegisterClassA_fn)Iat_hook::detour_iat_ptr("RegisterClassA", (void*)hk_RegisterClassA);
                    oRegisterClassW = (RegisterClassW_fn)Iat_hook::detour_iat_ptr("RegisterClassW", (void*)hk_RegisterClassW);
                    oRegisterClassExA = (RegisterClassExA_fn)Iat_hook::detour_iat_ptr("RegisterClassExA", (void*)hk_RegisterClassExA);
                    oRegisterClassExW = (RegisterClassExW_fn)Iat_hook::detour_iat_ptr("RegisterClassExW", (void*)hk_RegisterClassExW);
                    oGetForegroundWindow = (GetForegroundWindow_fn)Iat_hook::detour_iat_ptr("GetForegroundWindow", (void*)hk_GetForegroundWindow);
                    oGetActiveWindow = (GetActiveWindow_fn)Iat_hook::detour_iat_ptr("GetActiveWindow", (void*)hk_GetActiveWindow);
                    oGetFocus = (GetFocus_fn)Iat_hook::detour_iat_ptr("GetFocus", (void*)hk_GetFocus);
                    oLoadLibraryA = (LoadLibraryA_fn)Iat_hook::detour_iat_ptr("LoadLibraryA", (void*)hk_LoadLibraryA);
                    oLoadLibraryW = (LoadLibraryW_fn)Iat_hook::detour_iat_ptr("LoadLibraryW", (void*)hk_LoadLibraryW);
                    oLoadLibraryExA = (LoadLibraryExA_fn)Iat_hook::detour_iat_ptr("LoadLibraryExA", (void*)hk_LoadLibraryExA);
                    oLoadLibraryExW = (LoadLibraryExW_fn)Iat_hook::detour_iat_ptr("LoadLibraryExW", (void*)hk_LoadLibraryExW);
                    oFreeLibrary = (FreeLibrary_fn)Iat_hook::detour_iat_ptr("FreeLibrary", (void*)hk_FreeLibrary);

                    Iat_hook::detour_iat_ptr("GetProcAddress", (void*)hk_GetProcAddress);
                    Iat_hook::detour_iat_ptr("GetProcAddress", (void*)hk_GetProcAddress, d3d9dll);

                    if (oGetForegroundWindow == NULL)
                        oGetForegroundWindow = (GetForegroundWindow_fn)Iat_hook::detour_iat_ptr("GetForegroundWindow", (void*)hk_GetForegroundWindow, d3d9dll);
                    else
                        Iat_hook::detour_iat_ptr("GetForegroundWindow", (void*)hk_GetForegroundWindow, d3d9dll);

                    HMODULE ole32 = GetModuleHandleA("ole32.dll");
                    if (ole32) {
                        if (oRegisterClassA == NULL)
                            oRegisterClassA = (RegisterClassA_fn)Iat_hook::detour_iat_ptr("RegisterClassA", (void*)hk_RegisterClassA, ole32);
                        else
                            Iat_hook::detour_iat_ptr("RegisterClassA", (void*)hk_RegisterClassA, ole32);
                        if (oRegisterClassW == NULL)
                            oRegisterClassW = (RegisterClassW_fn)Iat_hook::detour_iat_ptr("RegisterClassW", (void*)hk_RegisterClassW, ole32);
                        else
                            Iat_hook::detour_iat_ptr("RegisterClassW", (void*)hk_RegisterClassW, ole32);
                        if (oRegisterClassExA == NULL)
                            oRegisterClassExA = (RegisterClassExA_fn)Iat_hook::detour_iat_ptr("RegisterClassExA", (void*)hk_RegisterClassExA, ole32);
                        else
                            Iat_hook::detour_iat_ptr("RegisterClassExA", (void*)hk_RegisterClassExA, ole32);
                        if (oRegisterClassExW == NULL)
                            oRegisterClassExW = (RegisterClassExW_fn)Iat_hook::detour_iat_ptr("RegisterClassExW", (void*)hk_RegisterClassExW, ole32);
                        else
                            Iat_hook::detour_iat_ptr("RegisterClassExW", (void*)hk_RegisterClassExW, ole32);
                        if (oGetActiveWindow == NULL)
                            oGetActiveWindow = (GetActiveWindow_fn)Iat_hook::detour_iat_ptr("GetActiveWindow", (void*)hk_GetActiveWindow, ole32);
                        else
                            Iat_hook::detour_iat_ptr("GetActiveWindow", (void*)hk_GetActiveWindow, ole32);
                    }

                    HookImportedModules();
                }
            }
        }
        break;
        case DLL_PROCESS_DETACH:
        {
            if (mFPSLimitMode == FrameLimiter::FPSLimitMode::FPS_ACCURATE)
                timeEndPeriod(1);

            SpiderFov::StopToggleThread();

            if (d3d9dll)
                FreeLibrary(d3d9dll);
        }
        break;
    }
    return true;
}

HRESULT WINAPI Direct3DShaderValidatorCreate9()
{
    if (!m_pDirect3DShaderValidatorCreate9)
    {
        return E_FAIL;
    }

    return m_pDirect3DShaderValidatorCreate9();
}

HRESULT WINAPI PSGPError()
{
    if (!m_pPSGPError)
    {
        return E_FAIL;
    }

    return m_pPSGPError();
}

HRESULT WINAPI PSGPSampleTexture()
{
    if (!m_pPSGPSampleTexture)
    {
        return E_FAIL;
    }

    return m_pPSGPSampleTexture();
}

int WINAPI D3DPERF_BeginEvent(D3DCOLOR col, LPCWSTR wszName)
{
    if (!m_pD3DPERF_BeginEvent)
    {
        return NULL;
    }

    return m_pD3DPERF_BeginEvent(col, wszName);
}

int WINAPI D3DPERF_EndEvent()
{
    if (!m_pD3DPERF_EndEvent)
    {
        return NULL;
    }

    return m_pD3DPERF_EndEvent();
}

DWORD WINAPI D3DPERF_GetStatus()
{
    if (!m_pD3DPERF_GetStatus)
    {
        return NULL;
    }

    return m_pD3DPERF_GetStatus();
}

BOOL WINAPI D3DPERF_QueryRepeatFrame()
{
    if (!m_pD3DPERF_QueryRepeatFrame)
    {
        return FALSE;
    }

    return m_pD3DPERF_QueryRepeatFrame();
}

void WINAPI D3DPERF_SetMarker(D3DCOLOR col, LPCWSTR wszName)
{
    if (!m_pD3DPERF_SetMarker)
    {
        return;
    }

    return m_pD3DPERF_SetMarker(col, wszName);
}

void WINAPI D3DPERF_SetOptions(DWORD dwOptions)
{
    if (!m_pD3DPERF_SetOptions)
    {
        return;
    }

    return m_pD3DPERF_SetOptions(dwOptions);
}

void WINAPI D3DPERF_SetRegion(D3DCOLOR col, LPCWSTR wszName)
{
    if (!m_pD3DPERF_SetRegion)
    {
        return;
    }

    return m_pD3DPERF_SetRegion(col, wszName);
}

HRESULT WINAPI DebugSetLevel(DWORD dw1)
{
    if (!m_pDebugSetLevel)
    {
        return E_FAIL;
    }

    return m_pDebugSetLevel(dw1);
}

void WINAPI DebugSetMute()
{
    if (!m_pDebugSetMute)
    {
        return;
    }

    return m_pDebugSetMute();
}

int WINAPI Direct3D9EnableMaximizedWindowedModeShim(BOOL mEnable)
{
    if (!m_pDirect3D9EnableMaximizedWindowedModeShim)
    {
        return NULL;
    }

    return m_pDirect3D9EnableMaximizedWindowedModeShim(mEnable);
}

IDirect3D9 *WINAPI Direct3DCreate9(UINT SDKVersion)
{
    if (!m_pDirect3DCreate9)
    {
        return nullptr;
    }

    IDirect3D9 *pD3D9 = m_pDirect3DCreate9(SDKVersion);

    if (pD3D9)
    {
        return new m_IDirect3D9Ex((IDirect3D9Ex*)pD3D9, IID_IDirect3D9);
    }

    return nullptr;
}

HRESULT WINAPI Direct3DCreate9Ex(UINT SDKVersion, IDirect3D9Ex **ppD3D)
{
    if (!m_pDirect3DCreate9Ex)
    {
        return E_FAIL;
    }

    HRESULT hr = m_pDirect3DCreate9Ex(SDKVersion, ppD3D);

    if (SUCCEEDED(hr) && ppD3D)
    {
        *ppD3D = new m_IDirect3D9Ex(*ppD3D, IID_IDirect3D9Ex);
    }

    return hr;
}
