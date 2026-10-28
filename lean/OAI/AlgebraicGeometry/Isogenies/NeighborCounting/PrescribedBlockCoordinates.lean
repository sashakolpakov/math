import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OppositeRestriction

/-! # Prescribed Block Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedBlockCoordinates

noncomputable section

/-! Actual coefficient sections of the original torsion functor.
Their product reconstructs the source section, and the prescribed
opposite sections lie in the actual canonical annihilators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.BlockPairing OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OppositeRestriction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Components

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

def prescribedBlockRepresentative (n : ℕ) (τ : Gal(E/ℚ)) (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X :=
  (AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).inv.app (.op T)
    ((PELModuli.CMPoints.BlockRetraction.torsionProjectionNat j iota hsplit A.abelian ρ n τ).app (.op T) x)

omit [IsAlgClosed k] in
theorem prescribedBlockRepresentative_point (n : ℕ) (τ : Gal(E/ℚ)) (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    Canonical.OppositeRestriction.originalBlockPoint j iota hsplit A ρ n τ T (prescribedBlockRepresentative j iota hsplit A ρ n τ T x) =
      AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T x :=
  congrArg ((PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota τ) n).app (.op T))
    (((AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).app (.op T)).inv_hom_id_apply _)

omit [IsAlgClosed k] in
theorem prescribedBlockRepresentative_inclusion (n : ℕ) (τ : Gal(E/ℚ)) (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    prescribedBlockRepresentative j iota hsplit A ρ n τ T x ≫
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n τ = x.val ≫ ρ.map (j.projector iota hsplit n τ) :=
  congrArg Subtype.val (prescribedBlockRepresentative_point j iota hsplit A ρ n τ T x)

omit [IsAlgClosed k] in
theorem prescribedBlockComponent_natural (n : ℕ) (τ : Gal(E/ℚ)) {T U : Over (Spec (.of k))}
    (t : U ⟶ T) (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    (A.abelian.torsionFunctor (q ^ n)).map t.op (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T x) =
      AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ U ((A.abelian.torsionFunctor (q ^ n)).map t.op x) := by
  apply Subtype.ext
  exact (Category.assoc t x.val (ρ.map (j.projector iota hsplit n τ))).symm

omit [IsAlgClosed k] in
theorem prescribedBlockRepresentative_after_baseChange (n : ℕ) (τ : Gal(E/ℚ))
    {T U : Over (Spec (.of k))} (t : U ⟶ T)
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    Canonical.OppositeRestriction.originalBlockPoint j iota hsplit A ρ n τ U
      (t ≫ prescribedBlockRepresentative j iota hsplit A ρ n τ T x) =
      AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ U ((A.abelian.torsionFunctor (q ^ n)).map t.op x) := by
  rw [← Canonical.OppositeRestriction.originalBlockPoint_natural, prescribedBlockRepresentative_point,
    prescribedBlockComponent_natural]

omit [IsAlgClosed k] in
theorem prescribed_components_product (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
    (T : Over (Spec (.of k))) (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    (∏ v : Fin s,
      (x.val ≫ ρ.map (j.projector iota hsplit n (labels (v, false)))) *
      (x.val ≫ ρ.map (j.projector iota hsplit n (labels (v, true))))) = x.val := by
  let a : T ⟶ A.abelian.scheme := x.val
  have hk : a ^ (q ^ n) = 1 := x.property
  have h := (Fintype.prod_equiv labels
    (fun v => a ≫ ρ.map (j.projector iota hsplit n (labels v)))
    (fun τ => a ≫ ρ.map (j.projector iota hsplit n τ)) (fun _ => rfl)).trans
      (PELModuli.CMPoints.BlockDecomposition.torsion_projectors_sum j iota hsplit A.abelian ρ n T a hk)
  rw [Fintype.prod_prod_type] at h
  simpa only [Fintype.prod_bool, mul_comm] using h

variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (H : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))

theorem prescribed_opposite_representative_mem {P : Over (Spec (.of k))}
    (T : Over (Spec (.of k))) (t : T ⟶ P) (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T))
    (hp : ∀ v : Fin s, ∀ (U : Over (Spec (.of k))) (u : U ⟶ T) (h : U ⟶ (H v).group.X),
      AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
        (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) U h)
        (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) U
          ((A.abelian.torsionFunctor (q ^ n)).map u.op x))) (v : Fin s) :
    prescribedBlockRepresentative j iota hsplit A ρ n (labels (v, true)) T x ∈
      ((Canonical.BlockPairing.prescribedOriginalBlockPairing j iota hsplit A ρ n
        (labels (v, false)) (labels (v, true))).relativeAnnihilator
          (Kernel.Base.fixedKernelFamily (P := P) (H v).inclusion.hom.hom)).points T t := by
  intro U u a ha
  obtain ⟨h, hh⟩ := ha
  change h ≫ (H v).inclusion.hom.hom = a at hh
  subst a
  have ho := hp v U u h
  rw [← prescribedBlockRepresentative_after_baseChange] at ho
  exact (Canonical.BlockPairing.canonicalTorsionOrthogonal_original_blocks j iota hsplit A ρ n
    (labels (v, false)) (labels (v, true)) U (h ≫ (H v).inclusion.hom.hom)
    (u ≫ prescribedBlockRepresentative j iota hsplit A ρ n (labels (v, true)) T x)).mp ho

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedBlockCoordinates
