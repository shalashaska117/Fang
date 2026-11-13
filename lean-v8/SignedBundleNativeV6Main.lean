/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import SignedBundleNativeV6Core
import NativeLimits

def main (args : List String) : IO UInt32 :=
  mainWithLimits Fang.NativeLimits.formulaDepthLimit Fang.NativeLimits.namingThreshold
    Fang.NativeLimits.certificateLimit args
