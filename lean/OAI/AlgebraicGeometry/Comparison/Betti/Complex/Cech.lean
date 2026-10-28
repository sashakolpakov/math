import OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCohomology
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComparisonNaturality

/-! # Cech -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Complex.Cech

noncomputable section

/-! Acyclic-cover Čech comparison for complex coefficient sheaves, natural in their actual maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)

abbrev ComplexSheaves (X : TopCat.{0}) := Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)

local instance : HasExt.{1} (ComplexSheaves X) := HasExt.standard _

def additiveSheaf (P : ComplexSheaves X) : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj P

def additiveMap {P Q : ComplexSheaves X} (f : P ⟶ Q) : additiveSheaf P ⟶ additiveSheaf Q :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).map f

def cohomology (P : ComplexSheaves X) (q : ℕ) : AddCommGrpCat.{0} :=
  ((cechComplexFunctor U).obj (additiveSheaf P).obj).homology q

def cohomologyMap {P Q : ComplexSheaves X} (f : P ⟶ Q) (q : ℕ) :
    cohomology U P q ⟶ cohomology U Q q :=
  HomologicalComplex.homologyMap ((cechComplexFunctor U).map (additiveMap f).hom) q

abbrev complexExt (P : ComplexSheaves X) (q : ℕ) :=
  Ext.{1} ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
    (ModuleCat.of ℂ ℂ)) P q

def additiveComparison (hU : iSup U = ⊤) (P : ComplexSheaves X)
    (hP : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U (additiveSheaf P)) (q : ℕ) :
    cohomology U P (q + 1) ≅ (Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)).obj
      (additiveSheaf P) :=
  SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections U (additiveSheaf P) hU hP q

def comparison (hU : iSup U = ⊤) (P : ComplexSheaves X)
    (hP : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U (additiveSheaf P)) (q : ℕ) :
    complexExt P (q + 1) ≃+ cohomology U P (q + 1) :=
  (SheafCohomology.complexSheafCohomologyForgetEquiv X P (q + 1)).trans
    (additiveComparison U hU P hP q).symm.addCommGroupIsoToAddEquiv

theorem inverse_square {A B C D : AddCommGrpCat.{0}}
    (e : A ≅ B) (e' : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : f ≫ e'.hom = e.hom ≫ g) : g ≫ e'.inv = e.inv ≫ f := by
  rw [e'.comp_inv_eq, Category.assoc, h]
  simp only [Iso.inv_hom_id_assoc]

theorem additiveComparison_naturality (hU : iSup U = ⊤) {P Q : ComplexSheaves X} (f : P ⟶ Q)
    (hP : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U (additiveSheaf P))
    (hQ : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U (additiveSheaf Q)) (q : ℕ) :
    cohomologyMap U f (q + 1) ≫ (additiveComparison U hU Q hQ q).hom =
      (additiveComparison U hU P hP q).hom ≫
        (Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)).map (additiveMap f) :=
  SheafCohomology.Cech.ComparisonNaturality.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections_naturality U (additiveMap f) hU hP hQ q

theorem additiveComparison_inv_naturality (hU : iSup U = ⊤) {P Q : ComplexSheaves X} (f : P ⟶ Q)
    (hP : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U (additiveSheaf P))
    (hQ : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U (additiveSheaf Q)) (q : ℕ)
    (x : Sheaf.H.{0} (additiveSheaf P) (q + 1)) :
    (additiveComparison U hU Q hQ q).inv
        (x.comp (Ext.mk₀ (additiveMap f)) (Nat.add_zero _)) =
      cohomologyMap U f (q + 1) ((additiveComparison U hU P hP q).inv x) := by
  let H := Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)
  have hi := inverse_square (additiveComparison U hU P hP q) (additiveComparison U hU Q hQ q)
    (cohomologyMap U f (q + 1)) (H.map (additiveMap f))
    (additiveComparison_naturality U hU f hP hQ q)
  have hx := congrArg
    (fun g : H.obj (additiveSheaf P) ⟶ cohomology U Q (q + 1) => g.hom x) hi
  exact hx

theorem comparison_naturality (hU : iSup U = ⊤) {P Q : ComplexSheaves X} (f : P ⟶ Q)
    (hP : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U (additiveSheaf P))
    (hQ : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U (additiveSheaf Q)) (q : ℕ)
    (x : complexExt P (q + 1)) :
    comparison U hU Q hQ q (x.comp (Ext.mk₀ f) (Nat.add_zero _)) =
      cohomologyMap U f (q + 1) (comparison U hU P hP q x) := by
  have hn := SheafCohomology.complexSheafCohomologyForgetEquiv_naturality X f (q + 1) x
  exact (congrArg (fun z => (additiveComparison U hU Q hQ q).inv z) hn).trans
    (additiveComparison_inv_naturality U hU f hP hQ q
      (SheafCohomology.complexSheafCohomologyForgetEquiv X P (q + 1) x))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Complex.Cech
