import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeSheafSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentEpimorphisms
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Generating Section Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeneratingSectionFiniteness

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite

universe u

variable {X : Scheme.{u}}

theorem affine_globalSections_finite_of_generatingSections
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (G : M.GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, ⊤) Γ(M, ⊤) := by
  have : Finite G.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite
  let L : X.Modules := SheafOfModules.free G.I
  let f : L ⟶ M := G.π
  let : Epi f := G.epi
  let : L.IsQuasicoherent := inferInstance
  have hL : Module.Finite Γ(X, ⊤) Γ(L, ⊤) := by
    change Module.Finite (X.ringCatSheaf.obj.obj (op ⊤))
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj
        (SheafOfModules.free G.I (R := X.ringCatSheaf)))
    exact HilbertConstruction.Finite.FreeSheafSections.finite_freeSheaf_globalSections X G.I
  let : Module.Finite Γ(X, ⊤) Γ(L, ⊤) := hL
  have hf : Epi f := inferInstance
  have hsurj : Function.Surjective (f.val.app (op ⊤)).hom := by
    exact @QuasicoherentEpimorphisms.quasicoherent_affine_surjective_of_epi X inferInstance
      L M f inferInstance inferInstance hf
  exact @Module.Finite.of_surjective
    _ _ _ _ _ _ _ _ _ _ _ hL (f.val.app (op ⊤)).hom hsurj

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeneratingSectionFiniteness
