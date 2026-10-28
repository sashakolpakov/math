import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricIsogeny
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Ordinary Quotients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryQuotients.Construction

noncomputable section

/-!
Geometric isogeny quotients preserve q-rank. Finiteness of source
q-torsion gives finite surjective multiplication by q, hence all required
division lifts. No ordinarity assertion about the quotient is an input.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))

omit [IsAlgClosed K] in
theorem e40_torsion_finite (q : ℕ) [IsFinite (A.torsionScheme q).hom] :
    IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme A.scheme q).hom := by
  have h := ArithmeticGeometry.OrdinaryLocus.Openness.FinitePresentation.Construction.torsion_isPullback A.scheme q
  have e := h.isoPullback_hom_snd
  let p : pullback (A.multiplication q).left η[A.scheme].left ⟶ Spec (.of K) :=
    pullback.snd (A.multiplication q).left η[A.scheme].left
  have : IsFinite p :=
    inferInstanceAs (IsFinite (A.torsionScheme q).hom)
  change h.isoPullback.hom ≫ p =
    (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme A.scheme q).hom at e
  let f : (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme A.scheme q).left ⟶
      pullback (A.multiplication q).left η[A.scheme].left := h.isoPullback.hom
  have : IsFinite f := inferInstanceAs (IsFinite h.isoPullback.hom)
  have hc : IsFinite (f ≫ p) := inferInstance
  exact (congrArg IsFinite e).mp hc

/-- Multiplication by q is finite and surjective as soon as its actual
torsion scheme is finite. This applies to the native ordinary splitting. -/
theorem multiplication_finite_surjective (q : ℕ) [IsFinite (A.torsionScheme q).hom] :
    IsFinite (A.multiplication q).left ∧ Surjective (A.multiplication q).left := by
  have : IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme A.scheme q).hom := e40_torsion_finite A q
  have hf : IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.multiplicationMap A.scheme q).left :=
    ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion A.scheme q
  exact ⟨hf, (ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat.Construction.surjective_flat_multiplication_of_isFinite A.scheme q).1⟩

/-- Every geometric point has a q-division lift, proved using the finite
surjective multiplication morphism and algebraic closedness. -/
theorem geometricPoints_divisible (q : ℕ) [IsFinite (A.torsionScheme q).hom] :
    Function.Surjective (fun x : A.Points (Over.mk (𝟙 (Spec (.of K)))) => x ^ q) := by
  have hf := multiplication_finite_surjective A q
  have : IsFinite (A.multiplication q).left := hf.1
  have : Surjective (A.multiplication q).left := hf.2
  intro y
  obtain ⟨x, hx⟩ := GeometricIsogeny.Construction.exists_geometric_lift (A.multiplication q).left y.left
  let z := (GeometricIsogeny.Construction.overGeometricFiberEquiv (A.multiplication q) (𝟙 _) y).symm ⟨x, hx⟩
  exact ⟨z.val, (A.comp_multiplication q z.val).symm.trans z.property⟩

/-- A quotient isogeny has the same geometric q-rank as the source. Only
the finite source torsion and the native isogeny hypotheses are needed. -/
theorem isogeny_qRank_preserved {h : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of K)))
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (q : ℕ) [IsFinite (A.torsionScheme q).hom] :
    Nat.card (A.torsionPoints q (Over.mk (𝟙 _))) =
      Nat.card (B.torsionPoints q (Over.mk (𝟙 _))) :=
  GeometricIsogeny.Construction.isogeny_geometric_qRank_preserved f (𝟙 _) q
    (fun k => geometricPoints_divisible A q k.val)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryQuotients.Construction
