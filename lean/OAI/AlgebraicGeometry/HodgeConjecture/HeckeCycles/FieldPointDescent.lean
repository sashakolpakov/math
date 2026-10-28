import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula

/-! # Field Point Descent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent.CM

noncomputable section

/-! Extension of the field of a test point is faithfully flat, hence
the original endomorphism equation descends from its geometric points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points

variable {K L : Type} [Field K] [Field L] (σ : K →+* L)
  {S : Scheme} (b : Spec (.of K) ⟶ S)

def testMap : Over.mk (Spec.map (CommRingCat.ofHom σ) ≫ b) ⟶ Over.mk b :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ)) rfl

instance testMap_epi : Epi (testMap σ b) := by
  let p := Spec.map (CommRingCat.ofHom σ)
  let : Flat p := inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom σ)))
  let : Surjective p := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  let : Epi p := Flat.epi_of_flat_of_surjective p
  let : Epi (testMap σ b).left := inferInstanceAs (Epi p)
  exact Over.epi_of_epi_left (testMap σ b)

theorem neighbor_formula_from_field_extension (G : CommGrp (Over S))
    {X : Over S} (a : X ⟶ G.X) (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (x y : Over.mk b ⟶ X) (Nx Ny : Multiset (Over.mk b ⟶ X))
    (h : PointSpecializationFormula.CM.Points.evaluateAt G (Over.mk (Spec.map (CommRingCat.ofHom σ) ≫ b)) f
      (Additive.ofMul ((testMap σ b ≫ x) ≫ a) - Additive.ofMul ((testMap σ b ≫ y) ≫ a)) =
      (Nx.map (fun z => Additive.ofMul ((testMap σ b ≫ z) ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul ((testMap σ b ≫ z) ≫ a))).sum) :
    PointSpecializationFormula.CM.Points.evaluateAt G (Over.mk b) f (Additive.ofMul (x ≫ a) - Additive.ofMul (y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul (z ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul (z ≫ a))).sum :=
  PointSpecializationFormula.CM.Descent.neighbor_formula_of_precompose G (testMap σ b) a f x y Nx Ny h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent.CM
