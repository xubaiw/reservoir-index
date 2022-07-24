/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Index

namespace Lake

/-! ## Module Facet Targets -/

/-- An opaque target thats build the module facet in a fresh build store. -/
@[inline] def Module.facetTarget (facet : Name) (self : Module)
[FamilyDef ModuleData facet (ActiveBuildTarget α)] : OpaqueTarget :=
  self.facet facet |>.target

/-! ## Pure Lean Lib Targets -/

@[inline] protected def LeanLib.leanTarget (self : LeanLib) : OpaqueTarget :=
  self.lean.target

/-! ## Native Lean Lib Targets -/

@[inline] protected def LeanLib.staticLibTarget (self : LeanLib) : FileTarget :=
  self.static.target.withInfo self.sharedLibFile

@[inline] protected def LeanLib.sharedLibTarget (self : LeanLib) : FileTarget :=
  self.shared.target.withInfo self.sharedLibFile

/-! ## Lean Executable Targets -/

@[inline] protected def LeanExe.build (self : LeanExe) : BuildM ActiveFileTarget :=
  self.exe.build

@[inline] protected def LeanExe.recBuild (self : LeanExe) : IndexBuildM ActiveFileTarget :=
  self.exe.recBuild

@[inline] protected def LeanExe.target (self : LeanExe) : FileTarget :=
  self.exe.target.withInfo self.file
