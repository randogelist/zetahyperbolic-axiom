@echo off
setlocal EnableExtensions DisableDelayedExpansion
set "PACKAGE_ROOT=%~dp0"
rem CALL reparses percent signs; delayed expansion reparses exclamation marks.
rem Reject these paths before either can corrupt the original path value.
for %%V in (PACKAGE_ROOT USERPROFILE LEAN_PAPER_CACHE LEAN_EXE LEAN433_EXE MATHLIB_CACHE MATHLIB_CACHE_ROOT MATHLIB_ROOT_OVERRIDE MATHLIB_OLEAN_DIR MATHLIB_DIR LEAN_PAPER_PACKAGES_DIR) do (
  set %%V 2>nul | "%SystemRoot%\System32\findstr.exe" /L /C:"!" /C:"%%" >nul
  if not errorlevel 1 goto UNSUPPORTED_PATH
)
setlocal EnableDelayedExpansion
rem Native Windows only. No Lake, Python, PowerShell, WSL or network setup.
rem COMPILED_ONLY receipts never certify a mathematical theorem. KernelAudit is final.
set "VERSION=v0_1_0_construction"
if exist "%~dp0VERSION" set /p VERSION=<"%~dp0VERSION"
set "PREFIX=GOODWORKFLOWFRONTIER::!VERSION!::"
set "SCHEMA=LEANED_PAPER_NATIVE_COMPILED_ONLY_SHA256_V1"
set "FLAGS=-j 16"
set "COMPILED=0"
set "REUSED=0"
set "REJECTED=0"
set "PROCESSED=0"
set "LOCK_HELD=0"
set "FAIL_REASON=UNSPECIFIED"
set "ORIGINAL_PATH=!PATH!"
set "CACHE_ROOT=%USERPROFILE%\lean-native\zetahyperbolic_leaned_paper_strict_v1"
if defined LEAN_PAPER_CACHE set "CACHE_ROOT=!LEAN_PAPER_CACHE!"
for %%D in ("!CACHE_ROOT!") do set "CACHE_ROOT=%%~fD"
if not exist "!PACKAGE_ROOT!modules.txt" (set "FAIL_REASON=MODULE_PLAN_MISSING"& goto FAILED)
if not exist "!PACKAGE_ROOT!targets.txt" (set "FAIL_REASON=AUDIT_TARGETS_MISSING"& goto FAILED)
if not exist "!PACKAGE_ROOT!src\LeanPaper\KernelAudit.lean" (set "FAIL_REASON=KERNEL_AUDIT_SOURCE_MISSING"& goto FAILED)
if not exist "!CACHE_ROOT!" mkdir "!CACHE_ROOT!"
if not exist "!CACHE_ROOT!" (set "FAIL_REASON=CACHE_DIRECTORY_UNAVAILABLE"& goto FAILED)
2>nul mkdir "!CACHE_ROOT!\writer.lock"
if errorlevel 1 (set "FAIL_REASON=CACHE_WRITER_LOCKED_OR_STALE_LOCK"& goto FAILED)
set "LOCK_HELD=1"
set "RUN_ROOT=!CACHE_ROOT!\runs\run_!RANDOM!_!RANDOM!_!RANDOM!"
if exist "!RUN_ROOT!" (set "FAIL_REASON=RUN_DIRECTORY_COLLISION"& goto FAILED)
mkdir "!RUN_ROOT!\view" "!RUN_ROOT!\accepted" "!RUN_ROOT!\stage" "!RUN_ROOT!\logs" >nul 2>&1
if not exist "!RUN_ROOT!\logs" (set "FAIL_REASON=RUN_DIRECTORY_UNAVAILABLE"& goto FAILED)
set "RECEIPT=!RUN_ROOT!\receipt.txt"
if exist "!PACKAGE_ROOT!audit.accepted" del /f /q "!PACKAGE_ROOT!audit.accepted" >nul 2>&1
if exist "!PACKAGE_ROOT!audit.accepted" (set "FAIL_REASON=PRIOR_PACKAGE_AUDIT_RECEIPT_LOCKED"& goto FAILED)
>"!RECEIPT!" echo !PREFIX!WORKFLOW=YOU_ARE_GOODWORKFLOWFRONTIER
if errorlevel 1 (set "FAIL_REASON=RECEIPT_UNAVAILABLE"& goto FAILED)
echo !PREFIX!WORKFLOW=YOU_ARE_GOODWORKFLOWFRONTIER
call :Emit MODE A_TIER_EXECUTION
call :Emit PACKAGE_STATUS CONSTRUCTION_PENDING_NATIVE_RESULTS
call :Emit CACHE_SCHEMA !SCHEMA!
call :Emit LEGACY_RECEIPTS REJECTED_UNVERIFIABLE_PROVENANCE_NOT_IMPORTED
call :Emit COMPILATION_ONLY_RECEIPTS NOT_PROOF_TIER_CERTIFICATION

if not defined LEAN_EXE if defined LEAN433_EXE set "LEAN_EXE=!LEAN433_EXE!"
if not defined LEAN_EXE if exist "%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe" set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
if not defined LEAN_EXE if exist "%USERPROFILE%\Downloads\lean-4.33.0-windows\bin\lean.exe" set "LEAN_EXE=%USERPROFILE%\Downloads\lean-4.33.0-windows\bin\lean.exe"
if not defined LEAN_EXE (set "FAIL_REASON=NATIVE_LEAN_EXE_NOT_FOUND_SET_LEAN_EXE"& goto FAILED)
if not exist "!LEAN_EXE!" (set "FAIL_REASON=NATIVE_LEAN_EXE_PATH_MISSING"& goto FAILED)
for %%E in ("!LEAN_EXE!") do set "LEAN_EXE=%%~fE"
for %%E in ("!LEAN_EXE!") do set "LEAN_BIN=%%~dpE"
for %%D in ("!LEAN_BIN!..") do set "TOOLCHAIN=%%~fD"
set "LEAN_SYSROOT=!TOOLCHAIN!"
set "CORE_LIB=!TOOLCHAIN!\lib\lean"
if not exist "!CORE_LIB!\Init.olean" (set "FAIL_REASON=NATIVE_TOOLCHAIN_STDLIB_MISSING_NO_ELAN_SHIM"& goto FAILED)
if not exist "!CORE_LIB!\Lean.olean" (set "FAIL_REASON=NATIVE_TOOLCHAIN_LEAN_LIBRARY_MISSING"& goto FAILED)
set "PATH=!LEAN_BIN!;!ORIGINAL_PATH!"
"!LEAN_EXE!" --version >"!RUN_ROOT!\lean-VERSION" 2>&1
if errorlevel 1 (set "FAIL_REASON=LEAN_VERSION_COMMAND_FAILED"& goto FAILED)
findstr /L /C:"version 4.33.0," "!RUN_ROOT!\lean-VERSION" >nul
if errorlevel 1 (set "FAIL_REASON=EXPECTED_EXACT_STABLE_LEAN_4_33_0"& goto FAILED)
findstr /I /L /C:"windows" "!RUN_ROOT!\lean-VERSION" >nul
if errorlevel 1 (set "FAIL_REASON=EXPECTED_NATIVE_WINDOWS_TOOLCHAIN"& goto FAILED)

set "MATHLIB_ROOT="
set "MATHLIB_PROJECT="
if defined MATHLIB_CACHE call :ConsiderMathlib "!MATHLIB_CACHE!"
if defined MATHLIB_CACHE_ROOT call :ConsiderMathlib "!MATHLIB_CACHE_ROOT!"
if defined MATHLIB_ROOT_OVERRIDE call :ConsiderMathlib "!MATHLIB_ROOT_OVERRIDE!"
if defined MATHLIB_OLEAN_DIR call :ConsiderMathlib "!MATHLIB_OLEAN_DIR!"
if defined MATHLIB_DIR call :ConsiderMathlib "!MATHLIB_DIR!"
call :ConsiderMathlib "%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1"
call :ConsiderMathlib "%USERPROFILE%\mathlib4"
call :ConsiderMathlib "%USERPROFILE%\Lean\mathlib4"
call :ConsiderMathlib "%USERPROFILE%\Downloads\mathlib4"
call :ConsiderMathlib "%USERPROFILE%\Downloads\mathlib"
if not defined MATHLIB_ROOT for /d %%D in ("%USERPROFILE%\lean-native\*") do if not defined MATHLIB_ROOT call :ConsiderMathlib "%%~fD"
if not defined MATHLIB_ROOT for /d %%D in ("%USERPROFILE%\Downloads\*") do if not defined MATHLIB_ROOT call :ConsiderMathlib "%%~fD"
if not defined MATHLIB_ROOT (set "FAIL_REASON=CACHED_MATHLIB_NOT_FOUND_SET_MATHLIB_CACHE"& goto FAILED)
rem Use only explicit package-cache directories, never arbitrary inherited project LEAN_PATH.
set "EXTERNAL_ROOTS=!RUN_ROOT!\external-roots.txt"
type nul >"!EXTERNAL_ROOTS!"
set "EXTERNAL_PATH="
call :AddExternal "!MATHLIB_ROOT!"
if errorlevel 1 (set "FAIL_REASON=EXTERNAL_ROOT_LIST_FAILED"& goto FAILED)
if defined MATHLIB_PROJECT for /d %%D in ("!MATHLIB_PROJECT!\.lake\packages\*") do (
  call :AddExternal "%%~fD\.lake\build\lib\lean"
  if errorlevel 1 (set "FAIL_REASON=EXTERNAL_ROOT_LIST_FAILED"& goto FAILED)
)
rem A Mathlib checkout can itself be a package of the cached project.
for %%D in ("!MATHLIB_ROOT!\..\..\..\..\..") do set "SIBLING_PACKAGES=%%~fD"
if exist "!SIBLING_PACKAGES!\mathlib\.lake\build\lib\lean\Mathlib.olean" for /d %%D in ("!SIBLING_PACKAGES!\*") do (
  call :AddExternal "%%~fD\.lake\build\lib\lean"
  if errorlevel 1 (set "FAIL_REASON=EXTERNAL_ROOT_LIST_FAILED"& goto FAILED)
)
if defined LEAN_PAPER_PACKAGES_DIR for /d %%D in ("!LEAN_PAPER_PACKAGES_DIR!\*") do (
  call :AddExternal "%%~fD\.lake\build\lib\lean"
  if errorlevel 1 (set "FAIL_REASON=EXTERNAL_ROOT_LIST_FAILED"& goto FAILED)
)
for %%D in ("!MATHLIB_ROOT!\..\..\..\..") do set "MATHLIB_CHECKOUT=%%~fD"
for /d %%D in ("!MATHLIB_CHECKOUT!\.lake\packages\*") do (
  call :AddExternal "%%~fD\.lake\build\lib\lean"
  if errorlevel 1 (set "FAIL_REASON=NESTED_MATHLIB_PACKAGE_ROOT_FAILED"& goto FAILED)
)
set "LEAN_PATH=!RUN_ROOT!\view;!EXTERNAL_PATH!;!CORE_LIB!"
set "LEAN_NUM_THREADS=16"
call :Emit ENVIRONMENT_CHECK HASHING_CACHED_BINARY_TREES_ONCE
set "ENV_FILE=!RUN_ROOT!\environment.txt"
>"!ENV_FILE!" echo SCHEMA=!SCHEMA!
>>"!ENV_FILE!" echo FLAGS=!FLAGS!
>>"!ENV_FILE!" echo LEAN_SYSROOT=!LEAN_SYSROOT!
>>"!ENV_FILE!" echo EXTERNAL_PATH=!EXTERNAL_PATH!
>>"!ENV_FILE!" echo PATH=!PATH!
>>"!ENV_FILE!" echo PROJECT_IMPORT_PATH=ISOLATED_VERIFIED_MODULE_VIEW
>>"!ENV_FILE!" echo LEAN_NUM_THREADS=!LEAN_NUM_THREADS!
type "!RUN_ROOT!\lean-VERSION" >>"!ENV_FILE!"
call :AppendHash "!PACKAGE_ROOT!run.cmd" "!ENV_FILE!" RUNNER
if errorlevel 1 (set "FAIL_REASON=RUNNER_HASH_FAILED"& goto FAILED)
call :AppendHash "!LEAN_EXE!" "!ENV_FILE!" COMPILER
if errorlevel 1 (set "FAIL_REASON=COMPILER_HASH_FAILED"& goto FAILED)
set "BINARY_COUNT=0"
call :HashTree "!LEAN_BIN!" "!ENV_FILE!"
if errorlevel 1 (set "FAIL_REASON=TOOLCHAIN_RUNTIME_HASH_FAILED"& goto FAILED)
call :HashTree "!CORE_LIB!" "!ENV_FILE!"
if errorlevel 1 (set "FAIL_REASON=STDLIB_HASH_FAILED"& goto FAILED)
for /f "usebackq delims=" %%D in ("!EXTERNAL_ROOTS!") do (
  call :HashTree "%%D" "!ENV_FILE!"
  if errorlevel 1 (set "FAIL_REASON=CACHED_EXTERNAL_OBJECT_HASH_FAILED"& goto FAILED)
)
call :HashFile "!ENV_FILE!"
if errorlevel 1 (set "FAIL_REASON=ENVIRONMENT_HASH_FAILED"& goto FAILED)
set "ENV_SHA=!HASH_RESULT!"
call :Emit ENVIRONMENT_SHA256 !ENV_SHA!
call :Emit ENVIRONMENT_BINARY_FILES !BINARY_COUNT!
set "LAST_MODULE="
set "MODULE_COUNT=0"
for /f "usebackq eol=# delims=" %%M in ("!PACKAGE_ROOT!modules.txt") do (
  set "LAST_MODULE=%%M"
  set /a MODULE_COUNT+=1 >nul
)
if not "!LAST_MODULE!"=="LeanPaper.KernelAudit" (set "FAIL_REASON=KERNEL_AUDIT_MUST_BE_FINAL_MODULE"& goto FAILED)
if "!MODULE_COUNT!"=="0" (set "FAIL_REASON=MODULE_PLAN_EMPTY"& goto FAILED)
for /f "usebackq eol=# delims=" %%M in ("!PACKAGE_ROOT!modules.txt") do (
  call :BuildModule "%%M"
  if errorlevel 1 goto FAILED
)
if not "!PROCESSED!"=="!MODULE_COUNT!" (set "FAIL_REASON=INCOMPLETE_MODULE_PLAN"& goto FAILED)
set "FINAL_LOG=!CACHE_ROOT!\state\LeanPaper.KernelAudit\compile.log"
findstr /X /L /C:"AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS" "!FINAL_LOG!" >nul
if errorlevel 1 (set "FAIL_REASON=FINAL_AXIOM_ALLOWLIST_SENTINEL_MISSING"& goto FAILED)
rem The final accepted receipt binds all content-verified module receipts.
set "AUDIT_RECEIPT=!RUN_ROOT!\audit.accepted"
>"!AUDIT_RECEIPT!" echo SCHEMA=!SCHEMA!
>>"!AUDIT_RECEIPT!" echo ENVIRONMENT_SHA256=!ENV_SHA!
call :AppendHash "!PACKAGE_ROOT!modules.txt" "!AUDIT_RECEIPT!" MODULE_PLAN
if errorlevel 1 (set "FAIL_REASON=AUDIT_PLAN_HASH_FAILED"& goto FAILED)
call :AppendHash "!PACKAGE_ROOT!targets.txt" "!AUDIT_RECEIPT!" AUDIT_TARGETS
if errorlevel 1 (set "FAIL_REASON=AUDIT_TARGET_HASH_FAILED"& goto FAILED)
for /f "usebackq eol=# delims=" %%M in ("!PACKAGE_ROOT!modules.txt") do (
  call :AppendHash "!RUN_ROOT!\accepted\%%M.receipt" "!AUDIT_RECEIPT!" "MODULE_%%M"
  if errorlevel 1 (set "FAIL_REASON=AUDIT_MODULE_RECEIPT_HASH_FAILED"& goto FAILED)
)
call :AppendHash "!FINAL_LOG!" "!AUDIT_RECEIPT!" AXIOM_AUDIT_LOG
if errorlevel 1 (set "FAIL_REASON=AUDIT_LOG_HASH_FAILED"& goto FAILED)
>>"!AUDIT_RECEIPT!" echo AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS
>>"!AUDIT_RECEIPT!" echo MANUSCRIPT_FULL_EQUIVALENCE=NOT_CERTIFIED_BY_RUNNER
if errorlevel 1 (set "FAIL_REASON=AUDIT_RECEIPT_COMMIT_FAILED"& goto FAILED)
copy /b /y "!AUDIT_RECEIPT!" "!PACKAGE_ROOT!audit.accepted.tmp" >nul
if errorlevel 1 (set "FAIL_REASON=PACKAGE_AUDIT_RECEIPT_COPY_FAILED"& goto FAILED)
fc /b "!AUDIT_RECEIPT!" "!PACKAGE_ROOT!audit.accepted.tmp" >nul 2>&1
if errorlevel 1 (set "FAIL_REASON=PACKAGE_AUDIT_RECEIPT_COPY_MISMATCH"& goto FAILED)
move /y "!PACKAGE_ROOT!audit.accepted.tmp" "!PACKAGE_ROOT!audit.accepted" >nul
if errorlevel 1 (set "FAIL_REASON=PACKAGE_AUDIT_RECEIPT_RENAME_FAILED"& goto FAILED)
call :Emit AXIOM_AUDIT PASS_ALL_PROJECT_DECLARATIONS_ALLOWLIST
call :Emit MANUSCRIPT_FULL_EQUIVALENCE OPEN_OR_PARTIAL
call :Emit NEW_NATIVE_COMPILED !COMPILED!
call :Emit VERIFIED_COMPILE_REUSED !REUSED!
call :Emit REUSE_REJECTED !REJECTED!
call :Emit MODULES_PROCESSED !PROCESSED!
call :Emit SUMMARY NATIVE_BUILD_AND_AXIOM_AUDIT_PASS
copy /y "!RECEIPT!" "!PACKAGE_ROOT!BUILD_RECEIPT.txt" >nul
if "!LOCK_HELD!"=="1" rd "!CACHE_ROOT!\writer.lock" >nul 2>&1
exit /b 0

:BuildModule
set "MODULE=%~1"
set "REL=!MODULE:.=\!"
set "SOURCE=!PACKAGE_ROOT!src\!REL!.lean"
set "DEPS=!PACKAGE_ROOT!dependencies\!MODULE!.txt"
set "STATE=!CACHE_ROOT!\state\!MODULE!"
set "OBJECT=!CACHE_ROOT!\objects\!REL!.olean"
set "ACCEPTED=!RUN_ROOT!\accepted\!MODULE!.receipt"
set "INPUTS=!RUN_ROOT!\stage\!MODULE!.inputs"
set "OUTPUTS=!RUN_ROOT!\stage\!MODULE!.outputs"
set "CACHED_OUTPUTS=!RUN_ROOT!\stage\!MODULE!.cached-outputs"
if exist "!ACCEPTED!" (set "FAIL_REASON=DUPLICATE_MODULE_!MODULE!"& exit /b 1)
if not exist "!SOURCE!" (set "FAIL_REASON=SOURCE_MISSING_!MODULE!"& exit /b 1)
if not exist "!DEPS!" (set "FAIL_REASON=DEPENDENCY_PLAN_MISSING_!MODULE!"& exit /b 1)
>"!INPUTS!" echo SCHEMA=!SCHEMA!
>>"!INPUTS!" echo MODULE=!MODULE!
>>"!INPUTS!" echo ENV_SHA256=!ENV_SHA!
>>"!INPUTS!" echo FLAGS=!FLAGS!
call :AppendHash "!SOURCE!" "!INPUTS!" SOURCE
if errorlevel 1 (set "FAIL_REASON=SOURCE_HASH_FAILED_!MODULE!"& exit /b 1)
set "SOURCE_SHA_BEFORE=!HASH_RESULT!"
call :AppendHash "!DEPS!" "!INPUTS!" DIRECT_LOCAL_DEPENDENCY_PLAN
if errorlevel 1 (set "FAIL_REASON=DEPENDENCY_PLAN_HASH_FAILED_!MODULE!"& exit /b 1)
set "DEPS_SHA_BEFORE=!HASH_RESULT!"
for /f "usebackq eol=# delims=" %%D in ("!DEPS!") do (
  if not exist "!RUN_ROOT!\accepted\%%D.receipt" (set "FAIL_REASON=DEPENDENCY_NOT_VERIFIED_BEFORE_!MODULE!_%%D"& exit /b 1)
  call :AppendHash "!RUN_ROOT!\accepted\%%D.receipt" "!INPUTS!" "DEPENDENCY_%%D"
  if errorlevel 1 (set "FAIL_REASON=DEPENDENCY_RECEIPT_HASH_FAILED_!MODULE!"& exit /b 1)
)
if "!MODULE!"=="LeanPaper.KernelAudit" (
  call :AppendHash "!PACKAGE_ROOT!modules.txt" "!INPUTS!" WHOLE_PLAN
  if errorlevel 1 (set "FAIL_REASON=FINAL_PLAN_HASH_FAILED"& exit /b 1)
  call :AppendHash "!PACKAGE_ROOT!targets.txt" "!INPUTS!" AUDIT_TARGETS
  if errorlevel 1 (set "FAIL_REASON=FINAL_TARGET_HASH_FAILED"& exit /b 1)
  rem Bind all active modules even if the import plan accidentally omits one.
  for /f "usebackq eol=# delims=" %%D in ("!PACKAGE_ROOT!modules.txt") do if not "%%D"=="LeanPaper.KernelAudit" (
    if not exist "!RUN_ROOT!\accepted\%%D.receipt" (set "FAIL_REASON=FINAL_MODULE_RECEIPT_MISSING_%%D"& exit /b 1)
    call :AppendHash "!RUN_ROOT!\accepted\%%D.receipt" "!INPUTS!" "WHOLE_MODULE_%%D"
    if errorlevel 1 (set "FAIL_REASON=FINAL_MODULE_HASH_FAILED"& exit /b 1)
  )
)
call :NativeDependencies
if errorlevel 1 exit /b 1
set "CAN_REUSE=0"
set "HAD_CACHE=0"
if exist "!OBJECT!" set "HAD_CACHE=1"
if exist "!STATE!\compiled.ok" set "HAD_CACHE=1"
if exist "!STATE!\compiled.ok" if exist "!STATE!\inputs.txt" if exist "!STATE!\outputs.txt" if exist "!STATE!\compile.log" if exist "!OBJECT!" (
  findstr /X /L /C:"!SCHEMA!;NATIVE_COMPILED_ONLY" "!STATE!\compiled.ok" >nul
  if not errorlevel 1 (
    fc /b "!INPUTS!" "!STATE!\inputs.txt" >nul 2>&1
    if not errorlevel 1 (
      call :ObjectManifest "!OBJECT!" "!STATE!\compile.log" "!CACHED_OUTPUTS!"
      if not errorlevel 1 (
        fc /b "!CACHED_OUTPUTS!" "!STATE!\outputs.txt" >nul 2>&1
        if not errorlevel 1 set "CAN_REUSE=1"
      )
    )
  )
)
if "!CAN_REUSE!"=="1" (
  set /a REUSED+=1 >nul
  call :Emit MODULE_!MODULE!_STATE COMPILED_ONLY_REUSE_VERIFIED_AUDIT_PENDING
) else (
  if "!HAD_CACHE!"=="1" set /a REJECTED+=1 >nul
  if "!HAD_CACHE!"=="1" call :Emit MODULE_!MODULE!_REUSE_REJECTION MISSING_OR_MISMATCHED_CONTENT_PROVENANCE
  set "STAGED=!RUN_ROOT!\stage\objects\!REL!.olean"
  set "BUILD_LOG=!RUN_ROOT!\logs\!MODULE!.log"
  for %%D in ("!STAGED!") do if not exist "%%~dpD" mkdir "%%~dpD" >nul 2>&1
  if not exist "!STATE!" mkdir "!STATE!" >nul 2>&1
  for %%D in ("!OBJECT!") do if not exist "%%~dpD" mkdir "%%~dpD" >nul 2>&1
  pushd "!PACKAGE_ROOT!src"
  if errorlevel 1 (set "FAIL_REASON=SOURCE_ROOT_UNAVAILABLE"& exit /b 1)
  "!LEAN_EXE!" !FLAGS! -o "!STAGED!" "!SOURCE!" >"!BUILD_LOG!" 2>&1
  set "COMPILER_EXIT=!ERRORLEVEL!"
  popd
  if not "!COMPILER_EXIT!"=="0" (
    if exist "!BUILD_LOG!" type "!BUILD_LOG!"
    set "FAIL_REASON=NATIVE_COMPILER_FAILURE_!MODULE!"
    exit /b 1
  )
  call :ObjectManifest "!STAGED!" "!BUILD_LOG!" "!OUTPUTS!"
  if errorlevel 1 (set "FAIL_REASON=NATIVE_OUTPUT_HASH_OR_PRESENCE_FAILED_!MODULE!"& exit /b 1)
  if "!MODULE!"=="LeanPaper.KernelAudit" (
    findstr /X /L /C:"AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS" "!BUILD_LOG!" >nul
    if errorlevel 1 (type "!BUILD_LOG!"& set "FAIL_REASON=FINAL_AXIOM_AUDIT_DID_NOT_ACCEPT"& exit /b 1)
  )
  call :CheckInputsUnchanged
  if errorlevel 1 exit /b 1
  rem Invalidate the previous commit marker before replacing any cached byte.
  if exist "!STATE!\compiled.ok" del /f /q "!STATE!\compiled.ok" >nul 2>&1
  if exist "!STATE!\compiled.ok" (set "FAIL_REASON=OLD_RECEIPT_LOCKED_!MODULE!"& exit /b 1)
  set "OBJECT_BASE=!OBJECT:~0,-6!"
  set "STAGED_BASE=!STAGED:~0,-6!"
  for %%S in (.olean .olean.private .olean.server .ilean .ir .ir.sig) do (
    if exist "!OBJECT_BASE!%%S" del /f /q "!OBJECT_BASE!%%S" >nul 2>&1
    if exist "!OBJECT_BASE!%%S" (set "FAIL_REASON=OLD_OBJECT_LOCKED_!MODULE!"& exit /b 1)
    if exist "!STAGED_BASE!%%S" (
      copy /b /y "!STAGED_BASE!%%S" "!OBJECT_BASE!%%S" >nul
      if errorlevel 1 (set "FAIL_REASON=OBJECT_PUBLICATION_FAILED_!MODULE!"& exit /b 1)
    )
  )
  copy /b /y "!BUILD_LOG!" "!STATE!\compile.log" >nul
  if errorlevel 1 (set "FAIL_REASON=LOG_PUBLICATION_FAILED_!MODULE!"& exit /b 1)
  call :ObjectManifest "!OBJECT!" "!STATE!\compile.log" "!CACHED_OUTPUTS!"
  if errorlevel 1 (set "FAIL_REASON=PUBLISHED_OBJECT_VERIFICATION_FAILED_!MODULE!"& exit /b 1)
  fc /b "!OUTPUTS!" "!CACHED_OUTPUTS!" >nul 2>&1
  if errorlevel 1 (set "FAIL_REASON=PUBLISHED_OBJECT_CONTENT_MISMATCH_!MODULE!"& exit /b 1)
  copy /b /y "!INPUTS!" "!STATE!\inputs.txt" >nul
  if errorlevel 1 (set "FAIL_REASON=INPUT_RECEIPT_PUBLICATION_FAILED_!MODULE!"& exit /b 1)
  copy /b /y "!OUTPUTS!" "!STATE!\outputs.txt" >nul
  if errorlevel 1 (set "FAIL_REASON=OUTPUT_RECEIPT_PUBLICATION_FAILED_!MODULE!"& exit /b 1)
  >"!STATE!\compiled.ok" echo !SCHEMA!;NATIVE_COMPILED_ONLY
  if errorlevel 1 (set "FAIL_REASON=COMPILE_RECEIPT_COMMIT_FAILED_!MODULE!"& exit /b 1)
  set /a COMPILED+=1 >nul
  call :Emit MODULE_!MODULE!_STATE NEW_NATIVE_COMPILED_AUDIT_PENDING
)
rem Dependencies see only objects verified during this run, never stale cache leftovers.
set "VIEW_OBJECT=!RUN_ROOT!\view\!REL!.olean"
for %%D in ("!VIEW_OBJECT!") do if not exist "%%~dpD" mkdir "%%~dpD" >nul 2>&1
set "OBJECT_BASE=!OBJECT:~0,-6!"
set "VIEW_BASE=!VIEW_OBJECT:~0,-6!"
call :CheckInputsUnchanged
if errorlevel 1 exit /b 1
for %%S in (.olean .olean.private .olean.server .ilean .ir .ir.sig) do if exist "!OBJECT_BASE!%%S" (
  copy /b /y "!OBJECT_BASE!%%S" "!VIEW_BASE!%%S" >nul
  if errorlevel 1 (set "FAIL_REASON=VERIFIED_IMPORT_VIEW_COPY_FAILED_!MODULE!"& exit /b 1)
  fc /b "!OBJECT_BASE!%%S" "!VIEW_BASE!%%S" >nul 2>&1
  if errorlevel 1 (set "FAIL_REASON=VERIFIED_IMPORT_VIEW_MISMATCH_!MODULE!"& exit /b 1)
)
copy /b "!STATE!\inputs.txt"+"!STATE!\outputs.txt" "!ACCEPTED!" >nul
if errorlevel 1 (set "FAIL_REASON=MODULE_RUN_RECEIPT_FAILED_!MODULE!"& exit /b 1)
set /a PROCESSED+=1 >nul
exit /b 0

:CheckInputsUnchanged
call :HashFile "!SOURCE!"
if errorlevel 1 (set "FAIL_REASON=SOURCE_RECHECK_HASH_FAILED_!MODULE!"& exit /b 1)
if /I not "!HASH_RESULT!"=="!SOURCE_SHA_BEFORE!" (set "FAIL_REASON=SOURCE_CHANGED_DURING_RUN_!MODULE!"& exit /b 1)
call :HashFile "!DEPS!"
if errorlevel 1 (set "FAIL_REASON=DEPENDENCY_PLAN_RECHECK_FAILED_!MODULE!"& exit /b 1)
if /I not "!HASH_RESULT!"=="!DEPS_SHA_BEFORE!" (set "FAIL_REASON=DEPENDENCY_PLAN_CHANGED_DURING_RUN_!MODULE!"& exit /b 1)
exit /b 0

:NativeDependencies
set "NATIVE_DEPS_LOG=!RUN_ROOT!\logs\!MODULE!.deps.log"
set "NATIVE_DEPS_ERROR=!RUN_ROOT!\logs\!MODULE!.deps.error.log"
set "NATIVE_LOCAL_LIST=!RUN_ROOT!\stage\!MODULE!.actual-local-imports"
type nul >"!NATIVE_LOCAL_LIST!"
pushd "!PACKAGE_ROOT!src"
if errorlevel 1 (set "FAIL_REASON=SOURCE_ROOT_UNAVAILABLE_FOR_DEPENDENCIES"& exit /b 1)
"!LEAN_EXE!" --deps "!SOURCE!" >"!NATIVE_DEPS_LOG!" 2>"!NATIVE_DEPS_ERROR!"
set "NATIVE_DEPS_EXIT=!ERRORLEVEL!"
popd
if not "!NATIVE_DEPS_EXIT!"=="0" (
  type "!NATIVE_DEPS_ERROR!"
  set "FAIL_REASON=NATIVE_IMPORT_RESOLUTION_FAILED_!MODULE!"
  exit /b 1
)
for /f "usebackq delims=" %%D in ("!NATIVE_DEPS_LOG!") do (
  call :BindNativeImport "%%D"
  if errorlevel 1 exit /b 1
)
for /f "usebackq eol=# delims=" %%D in ("!DEPS!") do (
  findstr /X /L /C:"%%D" "!NATIVE_LOCAL_LIST!" >nul
  if errorlevel 1 (set "FAIL_REASON=PLAN_DECLARES_NONIMPORT_!MODULE!_%%D"& exit /b 1)
)
exit /b 0

:BindNativeImport
set "NATIVE_IMPORT=%~1"
set "NATIVE_IMPORT=!NATIVE_IMPORT:/=\!"
if not exist "!NATIVE_IMPORT!" (set "FAIL_REASON=NATIVE_IMPORT_OBJECT_MISSING_!MODULE!"& exit /b 1)
set "NATIVE_LOCAL_REL=!NATIVE_IMPORT:%RUN_ROOT%\view\=!"
if not "!NATIVE_LOCAL_REL!"=="!NATIVE_IMPORT!" (
  set "ACTUAL_MODULE=!NATIVE_LOCAL_REL:~0,-6!"
  set "ACTUAL_MODULE=!ACTUAL_MODULE:\=.!"
  if not exist "!RUN_ROOT!\accepted\!ACTUAL_MODULE!.receipt" (set "FAIL_REASON=ACTUAL_IMPORT_HAS_NO_CURRENT_RECEIPT_!MODULE!"& exit /b 1)
  findstr /X /L /C:"!ACTUAL_MODULE!" "!DEPS!" >nul
  if errorlevel 1 (set "FAIL_REASON=PLAN_OMITS_ACTUAL_IMPORT_!MODULE!_!ACTUAL_MODULE!"& exit /b 1)
  >>"!NATIVE_LOCAL_LIST!" echo !ACTUAL_MODULE!
  call :AppendHash "!RUN_ROOT!\accepted\!ACTUAL_MODULE!.receipt" "!INPUTS!" "ACTUAL_IMPORT_!ACTUAL_MODULE!"
  if errorlevel 1 (set "FAIL_REASON=ACTUAL_LOCAL_IMPORT_HASH_FAILED_!MODULE!"& exit /b 1)
  exit /b 0
)
set "EXTERNAL_IMPORT_ALLOWED=0"
call :CheckExternalPrefix "!CORE_LIB!"
for /f "usebackq delims=" %%D in ("!EXTERNAL_ROOTS!") do call :CheckExternalPrefix "%%D"
if not "!EXTERNAL_IMPORT_ALLOWED!"=="1" (set "FAIL_REASON=ACTUAL_IMPORT_OUTSIDE_FINGERPRINTED_ROOTS_!MODULE!"& exit /b 1)
call :AppendHash "!NATIVE_IMPORT!" "!INPUTS!" "ACTUAL_EXTERNAL_IMPORT_!NATIVE_IMPORT!"
if errorlevel 1 (set "FAIL_REASON=ACTUAL_EXTERNAL_IMPORT_HASH_FAILED_!MODULE!"& exit /b 1)
exit /b 0

:CheckExternalPrefix
set "EXTERNAL_IMPORT_TAIL=!NATIVE_IMPORT:%~1\=!"
if not "!EXTERNAL_IMPORT_TAIL!"=="!NATIVE_IMPORT!" set "EXTERNAL_IMPORT_ALLOWED=1"
exit /b 0

:ObjectManifest
set "OM_OBJECT=%~1"
set "OM_LOG=%~2"
set "OM_DEST=%~3"
if not exist "!OM_OBJECT!" exit /b 1
for %%F in ("!OM_OBJECT!") do if %%~zF LEQ 0 exit /b 1
if not exist "!OM_LOG!" exit /b 1
>"!OM_DEST!" echo OBJECT_MANIFEST_V1
if errorlevel 1 exit /b 1
call :AppendHash "!OM_OBJECT!" "!OM_DEST!" OLEAN
if errorlevel 1 exit /b 1
set "OM_BASE=!OM_OBJECT:~0,-6!"
for %%S in (.olean.private .olean.server .ilean .ir .ir.sig) do (
  if exist "!OM_BASE!%%S" (
    call :AppendHash "!OM_BASE!%%S" "!OM_DEST!" "ARTIFACT%%S"
    if errorlevel 1 exit /b 1
  ) else (
    >>"!OM_DEST!" echo ARTIFACT%%S=ABSENT
    if errorlevel 1 exit /b 1
  )
)
call :AppendHash "!OM_LOG!" "!OM_DEST!" COMPILER_LOG
if errorlevel 1 exit /b 1
exit /b 0

:HashFile
set "HASH_RESULT="
if not exist "%~1" exit /b 1
certutil -hashfile "%~1" SHA256 >"!RUN_ROOT!\hash-output.txt" 2>&1
if errorlevel 1 exit /b 1
for /f "usebackq skip=1 delims=" %%H in ("!RUN_ROOT!\hash-output.txt") do if not defined HASH_RESULT set "HASH_RESULT=%%H"
set "HASH_RESULT=!HASH_RESULT: =!"
if "!HASH_RESULT:~63,1!"=="" exit /b 1
if not "!HASH_RESULT:~64,1!"=="" exit /b 1
>"!RUN_ROOT!\hash-digest.txt" echo !HASH_RESULT!
findstr /R /X "[0123456789abcdefABCDEF]*" "!RUN_ROOT!\hash-digest.txt" >nul
if errorlevel 1 exit /b 1
exit /b 0

:AppendHash
call :HashFile "%~1"
if errorlevel 1 exit /b 1
set "APPEND_LABEL=%~3"
>>"%~2" echo !APPEND_LABEL!=!HASH_RESULT!
if errorlevel 1 exit /b 1
exit /b 0

:HashTree
set "TREE_ROOT=%~1"
set "TREE_DEST=%~2"
set "TREE_LIST=!RUN_ROOT!\tree-files.txt"
set "TREE_SORTED=!RUN_ROOT!\tree-files-sorted.txt"
if not exist "!TREE_ROOT!\" exit /b 1
type nul >"!TREE_LIST!"
for /r "!TREE_ROOT!" %%F in (*.olean *.olean.private *.olean.server *.ilean *.ir *.ir.sig *.dll *.exe) do if exist "%%~fF" >>"!TREE_LIST!" echo %%~fF
sort "!TREE_LIST!" /o "!TREE_SORTED!"
if errorlevel 1 exit /b 1
>>"!TREE_DEST!" echo BINARY_TREE=!TREE_ROOT!
for /f "usebackq delims=" %%F in ("!TREE_SORTED!") do (
  call :AppendHash "%%F" "!TREE_DEST!" "FILE_%%F"
  if errorlevel 1 exit /b 1
  set /a BINARY_COUNT+=1 >nul
)
exit /b 0

:ConsiderMathlib
if defined MATHLIB_ROOT exit /b 0
if exist "%~1\Mathlib.olean" (
  for %%D in ("%~1") do set "MATHLIB_ROOT=%%~fD"
  for %%D in ("%~1\..\..\..\..") do if exist "%%~fD\.lake\build\lib\lean\Mathlib.olean" set "MATHLIB_PROJECT=%%~fD"
  exit /b 0
)
if exist "%~1\.lake\build\lib\lean\Mathlib.olean" (
  for %%D in ("%~1") do set "MATHLIB_PROJECT=%%~fD"
  set "MATHLIB_ROOT=!MATHLIB_PROJECT!\.lake\build\lib\lean"
  exit /b 0
)
if exist "%~1\.lake\packages\mathlib\.lake\build\lib\lean\Mathlib.olean" (
  for %%D in ("%~1") do set "MATHLIB_PROJECT=%%~fD"
  set "MATHLIB_ROOT=!MATHLIB_PROJECT!\.lake\packages\mathlib\.lake\build\lib\lean"
  exit /b 0
)
exit /b 0

:AddExternal
if not exist "%~1\" exit /b 0
for %%D in ("%~1") do set "EXTERNAL_CANDIDATE=%%~fD"
findstr /X /L /C:"!EXTERNAL_CANDIDATE!" "!EXTERNAL_ROOTS!" >nul 2>&1
if not errorlevel 1 exit /b 0
>>"!EXTERNAL_ROOTS!" echo !EXTERNAL_CANDIDATE!
if errorlevel 1 exit /b 1
if defined EXTERNAL_PATH (
  set "EXTERNAL_PATH=!EXTERNAL_PATH!;!EXTERNAL_CANDIDATE!"
) else (
  set "EXTERNAL_PATH=!EXTERNAL_CANDIDATE!"
)
exit /b 0

:Emit
echo !PREFIX!%~1=%~2
if defined RECEIPT >>"!RECEIPT!" echo !PREFIX!%~1=%~2
exit /b 0

:FAILED
call :Emit ERROR !FAIL_REASON!
call :Emit NEW_NATIVE_COMPILED !COMPILED!
call :Emit VERIFIED_COMPILE_REUSED !REUSED!
call :Emit REUSE_REJECTED !REJECTED!
call :Emit MODULES_PROCESSED !PROCESSED!
call :Emit SUMMARY NATIVE_BUILD_OR_AXIOM_AUDIT_FAILED
if defined RECEIPT if exist "!RECEIPT!" copy /y "!RECEIPT!" "!PACKAGE_ROOT!BUILD_RECEIPT.txt" >nul
if "!LOCK_HELD!"=="1" rd "!CACHE_ROOT!\writer.lock" >nul 2>&1
exit /b 1

:UNSUPPORTED_PATH
echo GOODWORKFLOWFRONTIER::v0_1_0_construction::ERROR=UNSUPPORTED_EXCLAMATION_OR_PERCENT_IN_PATH
 echo GOODWORKFLOWFRONTIER::v0_1_0_construction::SUMMARY=NATIVE_BUILD_OR_AXIOM_AUDIT_FAILED
exit /b 2
