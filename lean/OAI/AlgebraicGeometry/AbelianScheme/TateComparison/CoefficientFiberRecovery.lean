import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism

/-! # Coefficient Fiber Recovery -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CoefficientFiberRecovery

noncomputable section

section

/-! Naturality of the actual two-stage coefficient comparison for
endomorphisms already defined over the ground ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of R))) (s t : (Finset B)ᵒᵖ)

theorem twoStageCoefficientComparison_conjugation (f : A.scheme ⟶ A.scheme) :
    ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms (ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.twoStageCoefficientComparison R B A s t)
      (ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism (ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.twoStageCoefficientFamily R B A s t)
        (ArithmeticGeometry.Descent.CMVariety.AbelianCoefficientComparison.coefficientInclusion (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t)
        (ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism (A.pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop))
          (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t.unop)
          (ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism A (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f)))
      (ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism A (Spec.map (CommRingCat.ofHom (algebraMap R B))) f) :=
  ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms.trans
    (ArithmeticGeometry.Descent.CMVariety.AbelianCoefficientComparison.abelianCoefficientComparison (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B
      (A.pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)) t)
    (ArithmeticGeometry.Descent.CMVariety.AbelianCoefficientComparison.abelianCoefficientComparison R B A s) _ _ _
    (ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianCoefficientComparison_conjugation (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B
      (A.pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)) t
      (ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism A (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f))
    (ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianCoefficientComparison_conjugation R B A s f)

end

/-! Exact recovery of a field-fiber endomorphism from its descended
coefficient map, through the proved two-stage comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism

private theorem conjugation_injective {C : Type*} [Category* C] {X Y : C}
    (e : X ≅ Y) {f g : Y ⟶ Y}
    (h : e.hom ≫ f ≫ e.inv = e.hom ≫ g ≫ e.inv) : f = g := by
  have hh := congrArg (fun z => e.inv ≫ z ≫ e.hom) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using hh

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of R))) (s t : (Finset B)ᵒᵖ)

theorem coefficient_fiber_recovery (f : A.scheme ⟶ A.scheme)
    (c : (ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.twoStageCoefficientFamily R B A s t).scheme ⟶
      (ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.twoStageCoefficientFamily R B A s t).scheme)
    (a : (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).scheme ⟶
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).scheme)
    (hfc : ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism (A.pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop))
      (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t.unop)
      (ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism A (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f) = c)
    (ha : ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms (ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.twoStageCoefficientComparison R B A s t)
      (ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism (ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.twoStageCoefficientFamily R B A s t)
        (ArithmeticGeometry.Descent.CMVariety.AbelianCoefficientComparison.coefficientInclusion (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t) c) a) :
    ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism A (Spec.map (CommRingCat.ofHom (algebraMap R B))) f = a := by
  have hn := twoStageCoefficientComparison_conjugation R B A s t f
  have hc := congrArg (ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism (ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.twoStageCoefficientFamily R B A s t)
    (ArithmeticGeometry.Descent.CMVariety.AbelianCoefficientComparison.coefficientInclusion (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B t)) hfc
  exact conjugation_injective (ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.twoStageCoefficientComparison R B A s t)
    (hn.symm.trans (hc.trans ha))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CoefficientFiberRecovery
