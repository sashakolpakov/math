import OAI.AlgebraicGeometry.Comparison.Betti.Cech.Row
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalOpenSections

/-! # Cech -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.Cech

noncomputable section

/-! The actual Čech total of a complex with acyclic intersections compares with global sections of its functorial Godement total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex₂

open OAI.AlgebraicGeometry.Comparison.Betti.Cech.Row

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)
  (K : CochainComplex (FlasqueBiproduct.ComplexSheaves X) ℕ)

local instance godementCechForgetAdditive : (Complex.SheafForget.Flasque.sheafForget X).Additive :=
  Complex.SheafForget.Flasque.sheafForgetAdditive X

def additiveGodementComplex : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  ((Complex.SheafForget.Flasque.sheafForget X).mapHomologicalComplex (.up ℕ)).obj K

def additiveGodementTotalAugmentation : additiveGodementComplex K ⟶
    additiveGodementComplex (Bicomplex.godementTotal K) :=
  ((Complex.SheafForget.Flasque.sheafForget X).mapHomologicalComplex (.up ℕ)).map (Bicomplex.godementTotalAugmentation K)

def godementCechTotalMap :
    (FlasqueCechTotal.additiveSheafSectionCechBicomplex U (additiveGodementComplex K)).total (.up ℕ) ⟶
      (FlasqueCechTotal.additiveSheafSectionCechBicomplex U (additiveGodementComplex (Bicomplex.godementTotal K))).total (.up ℕ) :=
  total.map (Cech.Row.additiveSheafSectionCechBicomplexMap U (additiveGodementTotalAugmentation K)) (.up ℕ)

theorem godementCechTotalMap_quasiIso [Finite ι]
    (hK : ∀ r, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := X) U
      ((Complex.SheafForget.Flasque.sheafForget X).obj (K.X r))) : QuasiIso (godementCechTotalMap U K) := by
  apply Cech.Row.cechTotalMap_quasiIso_of_intersectionSections
  intro p t
  let V : Opens X := ∏ᶜ fun k : Fin (p + 1) => U (t k)
  let g := ((FlasqueBiproduct.sections V).mapHomologicalComplex (.up ℕ)).map (Bicomplex.godementTotalAugmentation K)
  have hg : QuasiIso g := TotalOpenSections.godementTotalAugmentation_openSections_quasiIso K V (fun r q => hK r p t q)
  have h := HomologicalComplex.quasiIso_map_of_preservesHomology g
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) (hφ := hg)
  exact h

theorem godementGlobalCechAugmentation_quasiIso (hU : ⨆ i, U i = ⊤) :
    QuasiIso (FlasqueCechTotal.globalCechTotalAugmentation U (additiveGodementComplex (Bicomplex.godementTotal K))) := by
  apply FlasqueCechTotal.globalCechTotalAugmentation_quasiIso U _ hU
  intro r
  have := TotalFlasque.godementTotal_isFlasque K r
  exact Complex.SheafForget.Flasque.sheafForgetFlasque ((Bicomplex.godementTotal K).X r)

def godementCechHomologyIso [Finite ι] (hU : ⨆ i, U i = ⊤)
    (hK : ∀ r, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := X) U
      ((Complex.SheafForget.Flasque.sheafForget X).obj (K.X r))) (n : ℕ) :
    ((FlasqueCechTotal.additiveSheafSectionCechBicomplex U (additiveGodementComplex K)).total (.up ℕ)).homology n ≅
      (FlasqueCechTotal.additiveGlobalComplex (additiveGodementComplex (Bicomplex.godementTotal K))).homology n := by
  have hf : QuasiIso (godementCechTotalMap U K) := godementCechTotalMap_quasiIso U K hK
  have hg : QuasiIso (FlasqueCechTotal.globalCechTotalAugmentation U (additiveGodementComplex (Bicomplex.godementTotal K))) :=
    godementGlobalCechAugmentation_quasiIso U K hU
  exact isoOfQuasiIsoAt (godementCechTotalMap U K) n ≪≫
    (isoOfQuasiIsoAt (FlasqueCechTotal.globalCechTotalAugmentation U (additiveGodementComplex (Bicomplex.godementTotal K))) n).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.Cech
