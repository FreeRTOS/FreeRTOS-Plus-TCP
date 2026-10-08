#!/usr/bin/env bash

set -euo pipefail

if [ "$#" -ne 4 ]; then
    echo "Usage: $0 FAMILY CMSIS_CORE_INCLUDE CMSIS_DEVICE_INCLUDE HAL_INCLUDE" >&2
    exit 2
fi

family="$1"
cmsis_core_include="$2"
cmsis_device_include="$3"
hal_include="$4"
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "${script_dir}/../../.." && pwd)"

case "${family}" in
    F1)
        hal_prefix="stm32f1xx"
        device_define="STM32F107xC"
        device_header="stm32f1xx.h"
        cpu="cortex-m3"
        ;;
    F2)
        hal_prefix="stm32f2xx"
        device_define="STM32F207xx"
        device_header="stm32f2xx.h"
        cpu="cortex-m3"
        ;;
    F4)
        hal_prefix="stm32f4xx"
        device_define="STM32F407xx"
        device_header="stm32f4xx.h"
        cpu="cortex-m4"
        ;;
    F7)
        hal_prefix="stm32f7xx"
        device_define="STM32F767xx"
        device_header="stm32f7xx.h"
        cpu="cortex-m7"
        ;;
    H5)
        hal_prefix="stm32h5xx"
        device_define="STM32H563xx"
        device_header="stm32h5xx.h"
        cpu="cortex-m33"
        ;;
    H7)
        hal_prefix="stm32h7xx"
        device_define="STM32H743xx"
        device_header="stm32h7xx.h"
        cpu="cortex-m7"
        ;;
    H7RS)
        hal_prefix="stm32h7rsxx"
        device_define="STM32H7S7xx"
        device_header="stm32h7rsxx.h"
        cpu="cortex-m7"
        ;;
    N6)
        hal_prefix="stm32n6xx"
        device_define="STM32N657xx"
        device_header="stm32n6xx.h"
        cpu="cortex-m55"
        ;;
    *)
        echo "Unsupported STM32 family: ${family}" >&2
        exit 2
        ;;
esac

for include_dir in "${cmsis_core_include}" "${cmsis_device_include}" "${hal_include}"; do
    if [ ! -d "${include_dir}" ]; then
        echo "Missing include directory: ${include_dir}" >&2
        exit 2
    fi
done

driver_dir="${repo_root}/source/portable/NetworkInterface/STM32/Drivers/${family}"
hal_config_dir="${script_dir}/hal-config/${family}"
build_dir="$(mktemp -d "${TMPDIR:-/tmp}/stm32-network-interface.XXXXXX")"
trap 'rm -rf -- "${build_dir}"' EXIT

compile_flags=(
    -std=c11
    -mcpu="${cpu}"
    -mthumb
    -Wall
    -Wextra
    -Werror
    -D"${device_define}"
    -DconfigMAX_SYSCALL_INTERRUPT_PRIORITY=0x50U
    -DconfigPRIO_BITS=4U
    -include "${device_header}"
    -I"${hal_config_dir}"
    -I"${driver_dir}"
    -I"${hal_include}"
    -I"${cmsis_device_include}"
    -I"${cmsis_core_include}"
    -I"${repo_root}/test/build-combination/Common"
    -I"${repo_root}/test/build-combination/AllEnable"
    -I"${repo_root}/test/unit-test/ConfigFiles"
    -I"${repo_root}/test/FreeRTOS-Kernel/include"
    -I"${repo_root}/source/include"
    -I"${repo_root}/source/portable/Compiler/GCC"
    -I"${repo_root}/source/portable/NetworkInterface/include"
)

sources=(
    "${repo_root}/source/portable/NetworkInterface/STM32/NetworkInterface.c"
    "${repo_root}/source/portable/NetworkInterface/Common/phyHandling.c"
    "${driver_dir}/${hal_prefix}_hal_eth.c"
)

if [ -f "${driver_dir}/${hal_prefix}_hal_eth_ex.c" ]; then
    sources+=( "${driver_dir}/${hal_prefix}_hal_eth_ex.c" )
fi

for source_file in "${sources[@]}"; do
    object_file="${build_dir}/$(basename "${source_file}" .c).o"
    echo "Compiling ${family}: ${source_file#"${repo_root}/"}"
    arm-none-eabi-gcc "${compile_flags[@]}" -c "${source_file}" -o "${object_file}"
done

if [ "${family}" = "F1" ]; then
    echo "Compiling ${family}: NetworkInterface.c with configuration overrides"
    arm-none-eabi-gcc \
        "${compile_flags[@]}" \
        -include "${script_dir}/override-config.h" \
        -c "${repo_root}/source/portable/NetworkInterface/STM32/NetworkInterface.c" \
        -o "${build_dir}/NetworkInterface-overrides.o"
fi

if [ "${family}" = "N6" ]; then
    echo "Compiling ${family}: NetworkInterface.c with RGMII enabled"
    arm-none-eabi-gcc \
        "${compile_flags[@]}" \
        -DipconfigUSE_RGMII=1 \
        -c "${repo_root}/source/portable/NetworkInterface/STM32/NetworkInterface.c" \
        -o "${build_dir}/NetworkInterface-RGMII.o"
fi
