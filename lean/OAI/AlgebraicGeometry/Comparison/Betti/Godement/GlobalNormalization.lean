import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Cech
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Hypercohomology

/-! # Global Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.GlobalNormalization

noncomputable section

/-! Normalize actual additive global sections of Godement totals against complex-valued global sections and integer extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ)

def additiveGlobalForgetIso :
    FlasqueCechTotal.additiveGlobalComplex (Cech.additiveGodementComplex K) ≅
      ((forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ)).obj
        (((FlasqueBiproduct.sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).obj K) :=
  (NatIso.mapHomologicalComplex
    (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop)
      (.up ℕ)).app (Cech.additiveGodementComplex K)

def additiveGlobalForgetHomologyEquiv (n : ℕ) :
    (FlasqueCechTotal.additiveGlobalComplex (Cech.additiveGodementComplex K)).homology n ≃+
      ((((FlasqueBiproduct.sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).obj K).homology n) := by
  let S := ((FlasqueBiproduct.sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).obj K
  let e := (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) n).mapIso (additiveGlobalForgetIso K)
  exact e.addCommGroupIsoToAddEquiv.trans
    (((S.sc n).mapHomologyIso (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).addCommGroupIsoToAddEquiv)

def natSectionsIntHomologyIso (n : ℕ) :
    (((FlasqueBiproduct.sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).obj K).homology n ≅
      (FlasqueHypercohomology.integerGlobalSectionsComplex (K.extend (ComplexShape.embeddingUpIntGE 0))).homology (n : ℤ) := by
  let H := FlasqueBiproduct.sections (⊤ : Opens X)
  have hH : H.Additive := FlasqueBiproduct.sectionsAdditive ⊤
  let S := (H.mapHomologicalComplex (.up ℕ)).obj K
  let e := Complex.Extension.mapExtendIso H (ComplexShape.embeddingUpIntGE 0) K
  exact (S.extendHomologyIso (ComplexShape.embeddingUpIntGE 0) (j := n) (j' := (n : ℤ)) (by simp)).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (.up ℤ) (n : ℤ)).mapIso e.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.GlobalNormalization
