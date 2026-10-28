import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.OpenSectionsQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Cech

/-! # Cech Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.CechQuasiIso

noncomputable section

/-! A sheaf quasi-isomorphism induces a quasi-isomorphism of actual
Čech totals when its terms are acyclic on the cover intersections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex₂

local instance (X : TopCat.{0}) :
    CategoryWithHomology (AlgebraicGeometry.Comparison.Betti.FlasqueBiproduct.ComplexSheaves X) :=
  inferInstanceAs (CategoryWithHomology
    (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)))

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)
  {K L : CochainComplex (AlgebraicGeometry.Comparison.Betti.FlasqueBiproduct.ComplexSheaves X) ℕ} (f : K ⟶ L)

local instance : (AlgebraicGeometry.Comparison.Betti.Complex.SheafForget.Flasque.sheafForget X).Additive := AlgebraicGeometry.Comparison.Betti.Complex.SheafForget.Flasque.sheafForgetAdditive X

def additiveMap : AlgebraicGeometry.Comparison.Betti.Godement.Cech.additiveGodementComplex K ⟶
    AlgebraicGeometry.Comparison.Betti.Godement.Cech.additiveGodementComplex L :=
  ((AlgebraicGeometry.Comparison.Betti.Complex.SheafForget.Flasque.sheafForget X).mapHomologicalComplex (.up ℕ)).map f

def cechMap :
    (AlgebraicGeometry.Comparison.Betti.FlasqueCechTotal.additiveSheafSectionCechBicomplex U
      (AlgebraicGeometry.Comparison.Betti.Godement.Cech.additiveGodementComplex K)).total (.up ℕ) ⟶
    (AlgebraicGeometry.Comparison.Betti.FlasqueCechTotal.additiveSheafSectionCechBicomplex U
      (AlgebraicGeometry.Comparison.Betti.Godement.Cech.additiveGodementComplex L)).total (.up ℕ) :=
  total.map (AlgebraicGeometry.Comparison.Betti.Cech.Row.additiveSheafSectionCechBicomplexMap U (additiveMap f)) (.up ℕ)

theorem cechMap_quasiIso [Finite ι] (hf : QuasiIso f)
    (hK : ∀ r, AlgebraicGeometry.SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U
      ((AlgebraicGeometry.Comparison.Betti.Complex.SheafForget.Flasque.sheafForget X).obj (K.X r)))
    (hL : ∀ r, AlgebraicGeometry.SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U
      ((AlgebraicGeometry.Comparison.Betti.Complex.SheafForget.Flasque.sheafForget X).obj (L.X r))) :
    QuasiIso (cechMap U f) := by
  apply AlgebraicGeometry.Comparison.Betti.Cech.Row.cechTotalMap_quasiIso_of_intersectionSections
  intro p t
  let V : Opens X := ∏ᶜ fun k : Fin (p + 1) => U (t k)
  let g := ((AlgebraicGeometry.Comparison.Betti.FlasqueBiproduct.sections V).mapHomologicalComplex (.up ℕ)).map f
  have hg : QuasiIso g := AlgebraicGeometry.Comparison.Betti.Acyclic.OpenSectionsQuasiIso.Godement.acyclic_openSections_quasiIso f hf V
    (fun r q => hK r p t q) (fun r q => hL r p t q)
  exact HomologicalComplex.quasiIso_map_of_preservesHomology g
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) (hφ := hg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.CechQuasiIso
