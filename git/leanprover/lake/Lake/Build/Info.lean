/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.LeanExe
import Lake.Config.ExternLib
import Lake.Build.Facets
import Lake.Util.EquipT

/-!
# Build Info

This module defines the Lake build info type and related utilities.
Build info is what is the data passed to a Lake build function to facilitate
the build.
-/

namespace Lake

/-- The type of Lake's build info. -/
inductive BuildInfo
| moduleFacet (module : Module) (facet : Name)
| packageFacet (package : Package) (facet : Name)
| staticLeanLib (lib : LeanLib)
| sharedLeanLib (lib : LeanLib)
| leanExe (exe : LeanExe)
| staticExternLib (lib : ExternLib)
| sharedExternLib (lib : ExternLib)
| customTarget (package : Package) (target : Name)

--------------------------------------------------------------------------------
/-! ## Build Info & Keys                                                      -/
--------------------------------------------------------------------------------

/-! ### Build Key Helper Constructors -/

abbrev Module.facetBuildKey (facet : Name) (self : Module) : BuildKey :=
  .moduleFacet self.keyName facet

abbrev Package.facetBuildKey (facet : Name) (self : Package) : BuildKey :=
  .packageFacet self.name facet

abbrev Package.targetBuildKey (target : Name) (self : Package) : BuildKey :=
  .customTarget self.name target

abbrev LeanLib.staticBuildKey (self : LeanLib) : BuildKey :=
  .targetFacet self.pkg.name self.name staticFacet

abbrev LeanLib.sharedBuildKey (self : LeanLib) : BuildKey :=
  .targetFacet self.pkg.name self.name sharedFacet

abbrev LeanExe.buildKey (self : LeanExe) : BuildKey :=
  .targetFacet self.pkg.name self.name exeFacet

abbrev ExternLib.staticBuildKey (self : ExternLib) : BuildKey :=
  .targetFacet self.pkg.name self.name staticFacet

abbrev ExternLib.sharedBuildKey (self : ExternLib) : BuildKey :=
  .targetFacet self.pkg.name self.name sharedFacet

/-! ### Build Info to Key -/

/-- The key that identifies the build in the Lake build store. -/
abbrev BuildInfo.key : (self : BuildInfo) → BuildKey
| moduleFacet m f => m.facetBuildKey f
| packageFacet p f => p.facetBuildKey f
| staticLeanLib l => l.staticBuildKey
| sharedLeanLib l => l.sharedBuildKey
| leanExe x => x.buildKey
| staticExternLib l => l.staticBuildKey
| sharedExternLib l => l.sharedBuildKey
| customTarget p t => p.targetBuildKey t

/-! ### Instances for deducing data types of `BuildInfo` keys -/

instance [FamilyDef ModuleData f α]
: FamilyDef BuildData (BuildInfo.key (.moduleFacet m f)) α where
  family_key_eq_type := by unfold BuildData; simp

instance [FamilyDef PackageData f α]
: FamilyDef BuildData (BuildInfo.key (.packageFacet p f)) α where
  family_key_eq_type := by unfold BuildData; simp

instance [FamilyDef CustomData (p.name, t) α]
: FamilyDef BuildData (BuildInfo.key (.customTarget p t)) α where
  family_key_eq_type := by unfold BuildData; simp

instance [FamilyDef TargetData LeanLib.staticFacet α]
: FamilyDef BuildData (BuildInfo.key (.staticLeanLib l)) α where
  family_key_eq_type := by unfold BuildData; simp

instance [FamilyDef TargetData LeanLib.sharedFacet α]
: FamilyDef BuildData (BuildInfo.key (.sharedLeanLib l)) α where
  family_key_eq_type := by unfold BuildData; simp

instance [FamilyDef TargetData LeanExe.exeFacet α]
: FamilyDef BuildData (BuildInfo.key (.leanExe x)) α where
  family_key_eq_type := by unfold BuildData; simp

instance [FamilyDef TargetData ExternLib.staticFacet α]
: FamilyDef BuildData (BuildInfo.key (.staticExternLib l)) α where
  family_key_eq_type := by unfold BuildData; simp

instance [FamilyDef TargetData ExternLib.sharedFacet α]
: FamilyDef BuildData (BuildInfo.key (.sharedExternLib l)) α where
  family_key_eq_type := by unfold BuildData; simp

--------------------------------------------------------------------------------
/-! ## Recursive Building                                                     -/
--------------------------------------------------------------------------------

/-- A build function for any element of the Lake build index. -/
abbrev IndexBuildFn (m : Type → Type v) :=
  -- `DBuildFn BuildInfo (BuildData ·.key) m` with less imports
  (info : BuildInfo) → m (BuildData info.key)

/-- A transformer to equip a monad with a build function for the Lake index. -/
abbrev IndexT (m : Type → Type v) := EquipT (IndexBuildFn m) m

/-- Build the given info using the Lake build index. -/
@[inline] def BuildInfo.recBuild (self : BuildInfo) [FamilyDef BuildData self.key α] : IndexT m α :=
  fun build => cast (by simp) <| build self

export BuildInfo (recBuild)

--------------------------------------------------------------------------------
/-! ## Build Info & Facets                                                    -/
--------------------------------------------------------------------------------

/-!
### Complex Builtin Facet Declarations

Additional builtin build data types on top of those defined in `FacetData` .
Defined here because they need to import configurations, whereas the definitions
there need to be imported by configurations.
-/

abbrev Module.importFacet := `lean.imports

/-- The direct × transitive imports of the Lean module. -/
module_data lean.imports : Array Module × Array Module

/-- The package's complete array of transitive dependencies. -/
package_data deps : Array Package


/-!
### Facet Build Info Helper Constructors

Definitions to easily construct `BuildInfo` values for module, package,
and target facets.
-/

namespace Module

/-- Build info for the module's specified facet. -/
abbrev facet (facet : Name) (self : Module) : BuildInfo :=
  .moduleFacet self facet

variable (self : Module)

abbrev imports  := self.facet importFacet
abbrev leanBin  := self.facet leanBinFacet
abbrev olean    := self.facet oleanFacet
abbrev ilean    := self.facet ileanFacet
abbrev c        := self.facet cFacet
abbrev o        := self.facet oFacet
abbrev dynlib   := self.facet dynlibFacet

end Module

/-- Build info for the package's specified facet. -/
abbrev Package.facet (facet : Name) (self : Package) : BuildInfo :=
  .packageFacet self facet

/-- Build info for the package's `extraDepTarget`. -/
abbrev Package.extraDep (self : Package) : BuildInfo :=
  self.facet `extraDep

/-- Build info for a custom package target. -/
abbrev Package.customTarget (target : Name) (self : Package) : BuildInfo :=
  .customTarget self target

/-- Build info of the Lean library's static binary. -/
abbrev LeanLib.static (self : LeanLib) : BuildInfo :=
  .staticLeanLib self

/-- Build info of the Lean library's shared binary. -/
abbrev LeanLib.shared (self : LeanLib) : BuildInfo :=
  .sharedLeanLib self

/-- Build info of the Lean executable. -/
abbrev LeanExe.exe (self : LeanExe) : BuildInfo :=
  .leanExe self

/-- Build info of the external library's static binary. -/
abbrev ExternLib.static (self : ExternLib) : BuildInfo :=
  .staticExternLib self

/-- Build info of the external library's shared binary. -/
abbrev ExternLib.shared (self : ExternLib) : BuildInfo :=
  .sharedExternLib self
