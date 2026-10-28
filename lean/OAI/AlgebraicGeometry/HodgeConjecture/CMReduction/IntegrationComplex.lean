import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Projection
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ComplexOperations
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.OppositePairs
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCupUnit

/-! # Integration Complex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.IntegrationComplex.CM.Construction

noncomputable section

section

/-! Complex integration along a connected projective factor. In particular,
the scalar left after eliminating a nonzero top class cannot vanish. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CartesianMonoidalCategory
open scoped TensorProduct

def complexFactorTrace (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    S.complexCohomology (S.complexDimension + S.complexDimension) →ₗ[ℂ]
      X.complexCohomology 0 :=
  (ComplexOperations.CM.Construction.projectiveComplexification X 0).toLinearMap.comp
    (((Projection.CM.Construction.factorTraceMap S X).baseChange ℂ).comp
      (ComplexOperations.CM.Construction.projectiveComplexification S (S.complexDimension + S.complexDimension)).symm.toLinearMap)

theorem complexFactorTrace_scalar (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace S.analyticSpace] [PathConnectedSpace X.analyticSpace]
    (b : S.complexCohomology (S.complexDimension + S.complexDimension)) (hb : b ≠ 0) :
    ∃ r : ℂ, r ≠ 0 ∧ complexFactorTrace S X b =
      r • AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) := by
  let bQ := (ComplexOperations.CM.Construction.projectiveComplexification S (S.complexDimension + S.complexDimension)).symm b
  have hbQ : bQ ≠ 0 := by
    intro hz
    apply hb
    exact (ComplexOperations.CM.Construction.projectiveComplexification S (S.complexDimension + S.complexDimension)).symm.injective
      (hz.trans (map_zero _).symm)
  obtain ⟨r, hr, heq⟩ := Projection.CM.Construction.coefficient_factorTrace_scalar ℂ S X bQ hbQ
  refine ⟨r, hr, ?_⟩
  change ComplexOperations.CM.Construction.projectiveComplexification X 0 ((Projection.CM.Construction.factorTraceMap S X).baseChange ℂ bQ) = _
  rw [heq, map_smul]
  change r • ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 0
    ((1 : ℂ) ⊗ₜ[ℚ] Cycles.Functoriality.UnitCap.cohomologyUnit X) = _
  rw [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul]
  exact congrArg (fun a => r • a) (ComplexMultiplication.HodgeComparison.RationalCupUnit.CM.Construction.rationalToComplexCohomology_unit _)

def factorProjectionPush (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).complexCohomology
      (S.complexDimension + S.complexDimension) →ₗ[ℂ] X.complexCohomology 0 := by
  let W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X
  let f : W.toOver ⟶ X.toOver := snd S.toOver X.toOver
  have hf : AlgebraicGeometry.IsProper f.left := SurfaceConstructionQ.CM.map_isProper (S := W) (X := X) f
  have hd : S.complexDimension + X.complexDimension = 0 + W.complexDimension := by
    dsimp [W]
    rw [Products.CM.SurfaceConstruction.product_complexDimension]
    omega
  exact ComplexOperations.CM.Construction.complexPushforward (X := W) (Y := X) f hf S.complexDimension 0 hd

def factorProjectionPull (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    S.complexCohomology (S.complexDimension + S.complexDimension) →ₗ[ℂ]
      (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).complexCohomology
        (S.complexDimension + S.complexDimension) :=
  (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (S.complexDimension + S.complexDimension)
    (fst S.toOver X.toOver)).hom

theorem complexFactorTrace_eq_pushforward (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : S.complexCohomology (S.complexDimension + S.complexDimension)) :
    complexFactorTrace S X b = factorProjectionPush S X (factorProjectionPull S X b) := by
  let j := ComplexOperations.CM.Construction.projectiveComplexification S (S.complexDimension + S.complexDimension)
  obtain ⟨t, rfl⟩ := j.surjective b
  let W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X
  let f : W.toOver ⟶ X.toOver := snd S.toOver X.toOver
  let g : W.toOver ⟶ S.toOver := fst S.toOver X.toOver
  have hf : AlgebraicGeometry.IsProper f.left := SurfaceConstructionQ.CM.map_isProper (S := W) (X := X) f
  have hd : S.complexDimension + X.complexDimension = 0 + W.complexDimension := by
    dsimp [W]
    rw [Products.CM.SurfaceConstruction.product_complexDimension]
    omega
  let Q := Cycles.Functoriality.UnitCap.cohomologyPushforward (X := W) (Y := X) f hf S.complexDimension 0 hd
  let P := (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (S.complexDimension + S.complexDimension) g).hom
  have hl : complexFactorTrace S X (j t) =
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 0
        (Q.baseChange ℂ (P.baseChange ℂ t)) := by
    change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 0
      ((Projection.CM.Construction.factorTraceMap S X).baseChange ℂ (j.symm (j t))) = _
    rw [LinearEquiv.symm_apply_apply]
    change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 0
      ((Q.comp P).baseChange ℂ t) = _
    rw [LinearMap.baseChange_comp]
    rfl
  have hpb := Pairs.CM.SurfaceConstruction.complexification_pullback
    (X := W) (Y := S) g (S.complexDimension + S.complexDimension) t
  have hpc := ComplexOperations.CM.Construction.complexPushforward_comparison (X := W) (Y := X)
    f hf S.complexDimension 0 hd (P.baseChange ℂ t)
  exact hl.trans (hpc.symm.trans (congrArg
    (ComplexOperations.CM.Construction.complexPushforward (X := W) (Y := X) f hf S.complexDimension 0 hd) hpb))

end

section

/-! The geometric projection formula on complex classes, and algebraicity
after eliminating a nonzero top-degree factor by native proper pushforward. -/

open _root_.CategoryTheory
open CartesianMonoidalCategory
open scoped TensorProduct

theorem bilinear_eq_of_rational_values
    {U V UC VC W : Type*}
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    [AddCommGroup UC] [Module ℂ UC] [AddCommGroup VC] [Module ℂ VC]
    [AddCommGroup W] [Module ℂ W]
    (j : ComplexMultiplication.WeightOne.CM.Complexification U ≃ₗ[ℂ] UC) (k : ComplexMultiplication.WeightOne.CM.Complexification V ≃ₗ[ℂ] VC)
    (F G : UC →ₗ[ℂ] VC →ₗ[ℂ] W)
    (h : ∀ u v, F (j ((1 : ℂ) ⊗ₜ[ℚ] u)) (k ((1 : ℂ) ⊗ₜ[ℚ] v)) =
      G (j ((1 : ℂ) ⊗ₜ[ℚ] u)) (k ((1 : ℂ) ⊗ₜ[ℚ] v))) : F = G := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨u, rfl⟩ := j.surjective x
  obtain ⟨v, rfl⟩ := k.surjective y
  induction u using TensorProduct.inductionOn with
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]
  | tmul a u =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp only [map_add, hv, hw]
    | tmul b v =>
      have hu : a ⊗ₜ[ℚ] u = a • ((1 : ℂ) ⊗ₜ[ℚ] u) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hv : b ⊗ₜ[ℚ] v = b • ((1 : ℂ) ⊗ₜ[ℚ] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hu, hv]
      simp only [map_smul, LinearMap.smul_apply, h]

theorem complexPushforward_rational {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : AlgebraicGeometry.IsProper f.left)
    (p q : ℕ) (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (a : X.rationalCohomology (p + p)) :
    ComplexOperations.CM.Construction.complexPushforward f hf p q hdeg (X.rationalCohomologyInclusion (p + p) a) =
      Y.rationalCohomologyInclusion (q + q) (Cycles.Functoriality.UnitCap.cohomologyPushforward f hf p q hdeg a) := by
  simpa only [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, LinearMap.baseChange_tmul,
    one_smul] using! ComplexOperations.CM.Construction.complexPushforward_comparison f hf p q hdeg ((1 : ℂ) ⊗ₜ[ℚ] a)

theorem complex_projection_top {W X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : W.toOver ⟶ X.toOver) (d p : ℕ)
    (hdim : W.complexDimension = X.complexDimension + d)
    (hp : p ≤ X.complexDimension)
    (a : X.complexCohomology (p + p)) (b : W.complexCohomology (d + d)) :
    ComplexOperations.CM.Construction.complexPushforward f (SurfaceConstructionQ.CM.map_isProper f) (p + d) p (by omega)
      (ComplexOperations.CM.Construction.evenCup ℂ (Betti.Scheme.schemePointSpace W.toOver) p d
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + p) f a) b) =
      ComplexOperations.CM.Construction.evenCup ℂ (Betti.Scheme.schemePointSpace X.toOver) p 0 a
        (ComplexOperations.CM.Construction.complexPushforward f (SurfaceConstructionQ.CM.map_isProper f) d 0 (by omega) b) := by
  let F := ((ComplexOperations.CM.Construction.evenCup ℂ (Betti.Scheme.schemePointSpace W.toOver) p d).compl₁₂
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + p) f).hom LinearMap.id).compr₂
      (ComplexOperations.CM.Construction.complexPushforward f (SurfaceConstructionQ.CM.map_isProper f) (p + d) p (by omega))
  let G := (ComplexOperations.CM.Construction.evenCup ℂ (Betti.Scheme.schemePointSpace X.toOver) p 0).compl₁₂ LinearMap.id
    (ComplexOperations.CM.Construction.complexPushforward f (SurfaceConstructionQ.CM.map_isProper f) d 0 (by omega))
  have hFG : F = G := by
    apply bilinear_eq_of_rational_values (ComplexOperations.CM.Construction.projectiveComplexification X (p + p))
      (ComplexOperations.CM.Construction.projectiveComplexification W (d + d))
    intro x y
    change ComplexOperations.CM.Construction.complexPushforward f _ (p + d) p _
      (ComplexOperations.CM.Construction.evenCup ℂ _ p d
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + p) f
          (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification _ (p + p) ((1 : ℂ) ⊗ₜ[ℚ] x)))
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification _ (d + d) ((1 : ℂ) ⊗ₜ[ℚ] y))) =
      ComplexOperations.CM.Construction.evenCup ℂ _ p 0
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification _ (p + p) ((1 : ℂ) ⊗ₜ[ℚ] x))
        (ComplexOperations.CM.Construction.complexPushforward f _ d 0 _
          (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification _ (d + d) ((1 : ℂ) ⊗ₜ[ℚ] y)))
    simp only [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul]
    have hf := (ConcreteCategory.congr_hom (Betti.Scheme.schemeBettiRationalInclusion_naturality f (p + p)) x).symm
    erw [hf]
    erw [← ComplexOperations.CM.Construction.rationalToComplex_evenCup (Betti.Scheme.schemePointSpace W.toOver) p d
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f x) y]
    have hcp := complexPushforward_rational (X := W) (Y := X) f
      (SurfaceConstructionQ.CM.map_isProper (S := W) (X := X) f) (p + d) p (by omega)
      (ComplexOperations.CM.Construction.evenCup ℚ (Betti.Scheme.schemePointSpace W.toOver) p d
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f x) y)
    have hcd := complexPushforward_rational (X := W) (Y := X) f
      (SurfaceConstructionQ.CM.map_isProper (S := W) (X := X) f) d 0 (by omega) y
    erw [hcp, hcd]
    erw [← ComplexOperations.CM.Construction.rationalToComplex_evenCup (Betti.Scheme.schemePointSpace X.toOver) p 0 x
      (Cycles.Functoriality.UnitCap.cohomologyPushforward (X := W) (Y := X) f
        (SurfaceConstructionQ.CM.map_isProper (S := W) (X := X) f) d 0 (by omega) y)]
    apply congrArg (X.rationalCohomologyInclusion (p + p))
    change Cycles.Functoriality.UnitCap.cohomologyPushforward f _ (p + d) p _
      (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast _ _ _ _) = _
    rw [ComplexOperations.CM.Construction.cohomologyCast_eq_cast]
    exact Projection.CM.Construction.native_projection_top f d p hdim hp x y
  exact LinearMap.congr_fun (LinearMap.congr_fun hFG a) b

end

/-! Eliminate a nonzero top-degree factor from an algebraic exterior class
by actual proper pushforward. The surviving class is recovered by dividing
the proved nonzero integration scalar. -/

open _root_.CategoryTheory
open CartesianMonoidalCategory

def factorExteriorCup (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (a : X.complexCohomology (p + p))
    (b : S.complexCohomology (S.complexDimension + S.complexDimension)) :
    (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).complexCohomology
      ((p + S.complexDimension) + (p + S.complexDimension)) :=
  ComplexOperations.CM.Construction.evenCup ℂ (Betti.Scheme.schemePointSpace (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).toOver)
    p S.complexDimension
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + p) (snd S.toOver X.toOver) a)
    (factorProjectionPull S X b)

theorem evenCup_unit_right (X : TopCat.{0}) (p : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X (p + p)) :
    ComplexOperations.CM.Construction.evenCup ℂ X p 0 a (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit X) = a := by
  change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X (p + p) 0 a (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit X) = a
  exact AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_cupUnit (R := ℂ) (p := p + p) (TopCat.toSSet.obj X) a

theorem algebraic_of_top_factor (h_Functoriality : CycleOperations.CM.Construction.FunctorialityInput)
    (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace S.analyticSpace] [PathConnectedSpace X.analyticSpace]
    (p : ℕ) (hp : p ≤ X.complexDimension)
    (a : X.complexCohomology (p + p))
    (b : S.complexCohomology (S.complexDimension + S.complexDimension)) (hb : b ≠ 0)
    (halg : factorExteriorCup S X p a b ∈
      (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).complexGeometricAlgebraicClasses
        (p + S.complexDimension)) :
    a ∈ X.complexGeometricAlgebraicClasses p := by
  let W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X
  let f : W.toOver ⟶ X.toOver := snd S.toOver X.toOver
  have hf : AlgebraicGeometry.IsProper f.left := SurfaceConstructionQ.CM.map_isProper (S := W) (X := X) f
  have hdim : W.complexDimension = X.complexDimension + S.complexDimension := by
    dsimp [W]
    rw [Products.CM.SurfaceConstruction.product_complexDimension, Nat.add_comm]
  obtain ⟨r, hr, htrace⟩ := complexFactorTrace_scalar S X b hb
  have htrace' : ComplexOperations.CM.Construction.complexPushforward (X := W) (Y := X) f hf S.complexDimension 0 (by omega)
      (factorProjectionPull S X b) =
        r • AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) := by
    change factorProjectionPush S X (factorProjectionPull S X b) = _
    rw [← complexFactorTrace_eq_pushforward S X b, htrace]
  have hproj := complex_projection_top (W := W) (X := X) f S.complexDimension p hdim hp
    a (factorProjectionPull S X b)
  rw [htrace', map_smul, evenCup_unit_right] at hproj
  have hpush := ComplexOperations.CM.Construction.complex_pushforward_algebraic h_Functoriality (X := W) (Y := X) f hf
    (p + S.complexDimension) p (by omega) (factorExteriorCup S X p a b) halg
  change ComplexOperations.CM.Construction.complexPushforward f hf (p + S.complexDimension) p _
    (ComplexOperations.CM.Construction.evenCup ℂ (Betti.Scheme.schemePointSpace W.toOver) p S.complexDimension
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + p) f a) (factorProjectionPull S X b)) ∈ _ at hpush
  rw [hproj] at hpush
  exact (X.complexGeometricAlgebraicClasses p).smul_mem_iff hr |>.mp hpush

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.IntegrationComplex.CM.Construction
