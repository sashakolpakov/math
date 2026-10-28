import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Submodule Sheaf Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SubmoduleSheafIs.Construction.SubmoduleSheaf

noncomputable section

/-! A local family of submodules of a module sheaf is itself a module sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} (M : X.Modules) (N : M.val.Submodule)

def IsLocal : Prop :=
  ∀ (ι : Type u) (U : ι → X.Opens) (s : Γ(M, iSup U)),
    (∀ i, M.presheaf.map (Opens.leSupr U i).op s ∈ N.obj (.op (U i))) →
      s ∈ N.obj (.op (iSup U))

theorem isSheaf (hN : IsLocal M N) :
    TopCat.Presheaf.IsSheaf (X := X) N.toPresheafOfModules.presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U s hs
  obtain ⟨t, ht, huniq⟩ := M.isSheaf.isSheafUniqueGluing U (fun i => (s i).val)
    (fun i j => congrArg Subtype.val (hs i j))
  have htN : t ∈ N.obj (.op (iSup U)) :=
    hN ι U t (fun i => (ht i).symm ▸ (s i).property)
  refine ⟨⟨t, htN⟩, fun i => Subtype.ext (ht i), ?_⟩
  intro z hz
  apply Subtype.ext
  exact huniq z.val (fun i => congrArg Subtype.val (hz i))

def ofLocal (hN : IsLocal M N) : X.Modules where
  val := N.toPresheafOfModules
  isSheaf := SubmoduleSheaf.isSheaf M N hN

def inclusion (hN : IsLocal M N) : ofLocal M N hN ⟶ M := ⟨N.ι⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SubmoduleSheafIs.Construction.SubmoduleSheaf
