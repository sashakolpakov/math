import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPoints

/-! # Prescribed Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedNaturality.Construction

noncomputable section

/-! The independent full-kernel prescription is stable under every
restriction of the test scheme, retaining its original chosen inclusions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (n : ℕ)

omit [IsAlgClosed k] in
theorem prescribedChosenPoint_natural (τ : Gal(E/ℚ))
    (H : FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
    {T U : Over (Spec (.of k))} (t : U ⟶ T) (a : T ⟶ H.group.X) :
    Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H U (t ≫ a) =
      (A.abelian.torsionFunctor (q ^ n)).map t.op
        (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H T a) :=
  (congrArg (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ U)
    (Category.assoc t a H.inclusion.hom.hom)).trans
    (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint_natural j iota hsplit A ρ n τ t (a ≫ H.inclusion.hom.hom))

variable (s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
  (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
    (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))

theorem prescribedKernelComponentCondition_natural
    {T U : Over (Spec (.of k))} (t : U ⟶ T)
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) (v : Fin s)
    (hx : CanonicalPoints.Construction.prescribedKernelComponentCondition j iota hsplit A ρ n s labels H T x v) :
    CanonicalPoints.Construction.prescribedKernelComponentCondition j iota hsplit A ρ n s labels H U
      ((A.abelian.torsionFunctor (q ^ n)).map t.op x) v := by
  constructor
  · obtain ⟨a, ha⟩ := hx.1
    exact ⟨t ≫ a, (prescribedChosenPoint_natural j iota hsplit A ρ n (labels (v, false)) (H v) t a).trans
      ((congrArg ((A.abelian.torsionFunctor (q ^ n)).map t.op) ha).trans
        (CanonicalBlockComponents.Construction.prescribedBlockComponent_natural j iota hsplit A ρ n (labels (v, false)) t x))⟩
  · intro V u a
    have hcomp : (A.abelian.torsionFunctor (q ^ n)).map u.op
        ((A.abelian.torsionFunctor (q ^ n)).map t.op x) =
      (A.abelian.torsionFunctor (q ^ n)).map (u ≫ t).op x :=
      Subtype.ext (Category.assoc u t x.val).symm
    exact (congrArg (fun y => Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) V
      (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) V a)
      (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) V y)) hcomp).mpr (hx.2 V (u ≫ t) a)

theorem prescribedFullKernel_torsion_components (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T))
    (hx : Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T x.val) :
    ∀ v, CanonicalPoints.Construction.prescribedKernelComponentCondition j iota hsplit A ρ n s labels H T x v := by
  obtain ⟨z, hz, hc⟩ := hx
  have he : z = x := Subtype.ext hz
  exact he ▸ hc

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedNaturality.Construction
