import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.DualAugmentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.ParameterKoszulResolution
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeDoubleDualComplex

/-! # Top Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.TopCohomology

noncomputable section

/-! The last cohomology of the dual scalar Koszul complex is the quotient by its parameters. This calculation uses the explicit first differential and needs no regularity assumption. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R]

def dualDifferentialCokernelCongr
    (C : CochainComplex (ModuleCat.{u} R) ℤ) {i j k l : ℤ}
    (hi : i = k) (hj : j = l) :
    cokernel (ModuleCat.ofHom (C.d i j).hom.dualMap) ≅
      cokernel (ModuleCat.ofHom (C.d k l).hom.dualMap) := by
  subst k
  subst l
  exact Iso.refl _

theorem scalarKoszulChainDual_isZero_above (rs : List R) (q : ℕ) (hq : rs.length < q) :
    IsZero ((Finite.FreeDoubleDualComplex.dualModuleComplexSymm (c := .up ℕ) (Regular.ParameterKoszulResolution.scalarKoszulChainComplex rs)).X q) := by
  have : Subsingleton ((KoszulComplex.scalarKoszulComplex (ModuleCat.of R R) rs).X (-(q : ℤ))) :=
    ModuleCat.subsingleton_of_isZero
      (KoszulComplex.scalarKoszulComplex_isZero_X (ModuleCat.of R R) rs (-(q : ℤ)) (Or.inl (by omega)))
  change IsZero (ModuleCat.of R
    (Module.Dual R ((KoszulComplex.scalarKoszulComplex (ModuleCat.of R R) rs).X (-(q : ℤ)))))
  exact ModuleCat.isZero_of_subsingleton _

def scalarKoszulDualTopHomologyIso (rs : List R) (g : ℕ)
    (hlen : rs.length = g) (hg : 0 < g) :
    (Finite.FreeDoubleDualComplex.dualModuleComplexSymm (c := .up ℕ) (Regular.ParameterKoszulResolution.scalarKoszulChainComplex rs)).homology g ≅
      ModuleCat.of R (R ⧸ Regular.SequenceBasic.Ideal.ofList rs) := by
  let K := KoszulComplex.scalarKoszulComplex (ModuleCat.of R R) rs
  let D := Finite.FreeDoubleDualComplex.dualModuleComplexSymm (c := .up ℕ) (Regular.ParameterKoszulResolution.scalarKoszulChainComplex rs)
  have hp : (ComplexShape.up ℕ).prev g = g - 1 :=
    ComplexShape.prev_eq' _ (by change g - 1 + 1 = g; omega)
  have hn : (ComplexShape.up ℕ).next g = g + 1 :=
    ComplexShape.next_eq' _ rfl
  have hz : IsZero (D.X (g + 1)) :=
    scalarKoszulChainDual_isZero_above rs (g + 1) (by omega)
  let E : D.homology g ≅ cokernel (D.d (g - 1) g) :=
    D.isoHomologyι g (g + 1) hn (hz.eq_of_tgt _ _) ≪≫
      D.opcyclesIsoSc' (g - 1) g (g + 1) hp hn ≪≫
      (D.sc' (g - 1) g (g + 1)).opcyclesIsoCokernel
  have hi : -(g : ℤ) = LowestTerm.scalarKoszulLowestIndex rs := by
    rw [LowestTerm.scalarKoszulLowestIndex_eq_neg_length, hlen]
  have hj : -((g - 1 : ℕ) : ℤ) = LowestTerm.scalarKoszulNextIndex rs := by
    have h := LowestTerm.scalarKoszulLowestIndex_add_one rs
    rw [LowestTerm.scalarKoszulLowestIndex_eq_neg_length, hlen] at h
    omega
  exact E ≪≫ dualDifferentialCokernelCongr K hi hj ≪≫ DualAugmentation.scalarKoszulDualCokernelQuotientIso rs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.TopCohomology
