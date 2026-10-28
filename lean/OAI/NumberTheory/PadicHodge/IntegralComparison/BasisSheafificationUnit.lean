import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.BasisSheafification
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.LocalizingBasis

/-! # Basis Sheafification Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BasisSheafificationUnit

noncomputable section

/-! The canonical sheafification unit is an isomorphism wherever a basis comparison is. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

section

universe u v w z

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}} {ι : Type z}
  (B : ι → Opens X) (hB : Opens.IsBasis (Set.range B))
  (P : X.Presheaf C) (F : TopCat.Sheaf C X)
  (e : (inducedFunctor B).op ⋙ P ≅ (inducedFunctor B).op ⋙ F.obj)
  [HasWeakSheafify (Opens.grothendieckTopology X) C]

theorem component (i : ι) :
    (toSheafify (Opens.grothendieckTopology X) P).app (op (B i)) ≫
      (Independent.BasisSheafification.iso B hB P F e).hom.hom.app (op (B i)) = e.hom.app (op i) := by
  change (toSheafify (Opens.grothendieckTopology X) P ≫
    sheafifyLift (Opens.grothendieckTopology X) (Independent.BasisSheafification.toSheaf B hB P F e)
      F.property).app (op (B i)) = _
  rw [toSheafify_sheafifyLift]
  exact Independent.BasisSheafification.toSheaf_app B hB P F e i

include hB e in
theorem isIso (i : ι) : IsIso ((toSheafify (Opens.grothendieckTopology X) P).app (op (B i))) := by
  let a := (Independent.BasisSheafification.iso B hB P F e).hom.hom.app (op (B i))
  have : IsIso a := (((sheafToPresheaf (Opens.grothendieckTopology X) C).mapIso
    (Independent.BasisSheafification.iso B hB P F e)).app (op (B i))).isIso_hom
  have : IsIso ((toSheafify (Opens.grothendieckTopology X) P).app (op (B i)) ≫ a) := by
    rw [show _ ≫ a = e.hom.app (op i) from component B hB P F e i]
    infer_instance
  exact IsIso.of_isIso_comp_right _ a

end

namespace Localizing

open _root_.AlgebraicGeometry

universe u

variable (A : CommRingCat.{u}) (P : (Spec A).Opensᵒᵖ ⥤ ModuleCat.{u} A)
  (hP : ∀ a : A, IsLocalizedModule (Submonoid.powers a)
    (P.map (PrimeSpectrum.basicOpen a).leTop.op).hom)

include hP in
theorem principal (a : A) :
    IsIso ((toSheafify (Opens.grothendieckTopology (Spec A)) P).app (op (PrimeSpectrum.basicOpen a))) :=
  isIso (fun a : A => (PrimeSpectrum.basicOpen a : (Spec A).Opens))
    PrimeSpectrum.isBasis_basic_opens P (Independent.LocalizingBasis.associatedSheaf A P)
    (Independent.LocalizingBasis.iso A P hP) a

include hP in
theorem top : IsIso ((toSheafify (Opens.grothendieckTopology (Spec A)) P).app (op ⊤)) := by
  have h := principal A P hP 1
  have hopen : (PrimeSpectrum.basicOpen (1 : A) : (Spec A).Opens) = ⊤ := PrimeSpectrum.basicOpen_one
  rwa [hopen] at h

end Localizing

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BasisSheafificationUnit
