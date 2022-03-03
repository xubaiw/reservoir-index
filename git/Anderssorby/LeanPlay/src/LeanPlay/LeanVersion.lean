import Blake3

namespace LeanPlay

def leanVersionStringCore :=
  s!"{Lean.version.major}.{Lean.version.minor}.{Lean.version.patch}"

def origin := "leanprover/lean4"

def leanVersionString :=
  if Lean.version.isRelease then
    s!"{origin}:{leanVersionStringCore}"
  else if Lean.version.specialDesc ≠ "" then
    s!"{origin}:{Lean.version.specialDesc}"
  else
    s!"{origin}:master"

def uiLeanVersionString :=
if Lean.version.isRelease then
  leanVersionStringCore
else if Lean.version.specialDesc ≠ "" then
  s!"{leanVersionStringCore}-{Lean.version.specialDesc}"
else
  s!"master ({leanVersionStringCore})"

def verifyLeanVersion : IO PUnit := do
  let out ← IO.Process.output {
    cmd := "lean",
    args := #["--version"]
  }
  if out.exitCode == 0 then
    unless out.stdout.drop 14 |>.startsWith uiLeanVersionString do
      throw <| IO.userError <|
        s!"expected {uiLeanVersionString}, but got {out.stdout.trim}"
  else
    throw <| IO.userError <| "missing lean!"

def version := s!"Lean: {uiLeanVersionString}
Blake3: {Blake3.version}"
