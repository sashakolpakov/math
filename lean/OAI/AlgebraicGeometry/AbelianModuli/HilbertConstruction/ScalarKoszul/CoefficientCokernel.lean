import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.AugmentationIdeal

/-! # Coefficient Cokernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.CoefficientCokernel

noncomputable section

/-! Coefficient-module isomorphisms transport the entire scalar Koszul
complex and its final cokernel. A rank-one coefficient module has the
actual parameter quotient as cokernel, which is nonzero for a proper ideal. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u

def cochainFinalCokernelIso {C : Type u} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (e : K ≅ L) :
    cokernel (K.d (-1) 0) ≅ cokernel (L.d (-1) 0) :=
  cokernel.mapIso _ _ ((HomologicalComplex.eval C (.up ℤ) (-1)).mapIso e)
    ((HomologicalComplex.eval C (.up ℤ) 0).mapIso e) (e.hom.comm (-1) 0).symm

def scalarKoszulCoefficientIso {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (e : M ≅ N) (rs : List R) :
    KoszulComplex.scalarKoszulComplex M rs ≅ KoszulComplex.scalarKoszulComplex N rs := by
  induction rs with
  | nil => exact (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).mapIso e
  | cons r rs ih =>
    exact HomologicalComplex.homotopyCofiber.mapArrowIso
      (r • 𝟙 (KoszulComplex.scalarKoszulComplex M rs)) (r • 𝟙 (KoszulComplex.scalarKoszulComplex N rs))
      (fun j => ⟨j - 1, by change j - 1 + 1 = j; omega⟩)
      (Arrow.isoMk ih ih (by
        change ih.hom ≫ (r • 𝟙 (KoszulComplex.scalarKoszulComplex N rs)) =
          (r • 𝟙 (KoszulComplex.scalarKoszulComplex M rs)) ≫ ih.hom
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]))

def scalarKoszulRankOneCokernelIso {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (e : M ≅ ModuleCat.of R R) (rs : List R) :
    cokernel ((KoszulComplex.scalarKoszulComplex M rs).d (-1) 0) ≅ ModuleCat.of R (R ⧸ Regular.SequenceBasic.Ideal.ofList rs) :=
  cochainFinalCokernelIso (scalarKoszulCoefficientIso e rs) ≪≫ AugmentationIdeal.scalarKoszulCokernelQuotientIso rs

theorem scalarKoszulRankOneCokernel_nonzero {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (e : M ≅ ModuleCat.of R R) (rs : List R) (hr : Regular.SequenceBasic.Ideal.ofList rs ≠ ⊤) :
    ¬ IsZero (cokernel ((KoszulComplex.scalarKoszulComplex M rs).d (-1) 0)) := by
  let : Nontrivial (R ⧸ Regular.SequenceBasic.Ideal.ofList rs) := Ideal.Quotient.nontrivial_iff.mpr hr
  intro hz
  have : Subsingleton (R ⧸ Regular.SequenceBasic.Ideal.ofList rs) :=
    ModuleCat.isZero_iff_subsingleton.mp ((scalarKoszulRankOneCokernelIso M e rs).isZero_iff.mp hz)
  exact zero_ne_one (Subsingleton.elim (0 : R ⧸ Regular.SequenceBasic.Ideal.ofList rs) 1)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.CoefficientCokernel
