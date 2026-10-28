import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TwistIteration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalenceCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CohomologyEulerAdditivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.QuotientFiniteType
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.FirstDifference
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.TwistEulerZero

/-! # Twist Euler Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.TwistEulerPolynomial

noncomputable section

/-! Euler polynomials for actual coherent twists transform by translation, positive-power dilation, and first difference under a regular-section CategoryTheory.Limits.cokernel sequence. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

def HasCoherentTwistEulerPolynomial (p : X ⟶ Spec (.of K))
    (M : X.Modules) (L : Line.Bundles.LineBundle X) (P : Polynomial ℚ) : Prop :=
  ∀ m : ℕ, P.eval (m : ℚ) = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (Tensor.ProductSheaf.tensorModule M (L.tensorPower m).sheaf) : ℚ)

def coherentTwistShiftIso (L : Line.Bundles.LineBundle X) (M : X.Modules) (m n : ℕ) :
    Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule M (L.tensorPower m).sheaf) (L.tensorPower n).sheaf ≅
      Tensor.ProductSheaf.tensorModule M (L.tensorPower (m + n)).sheaf :=
  ConcreteModuleTensorAssociativity.actualModuleTensorAssoc M (L.tensorPower m).sheaf (L.tensorPower n).sheaf ≪≫
    Tensor.Bifunctor.tensorModuleMapIso (Iso.refl M) (L.tensorPowerAddIso m n).symm

theorem HasCoherentTwistEulerPolynomial.shift
    {p : X ⟶ Spec (.of K)} {M : X.Modules} {L : Line.Bundles.LineBundle X} {P : Polynomial ℚ}
    (hP : HasCoherentTwistEulerPolynomial p M L P) (m : ℕ) :
    HasCoherentTwistEulerPolynomial p (Tensor.ProductSheaf.tensorModule M (L.tensorPower m).sheaf) L
      (P.comp (Polynomial.X + Polynomial.C (m : ℚ))) := by
  intro n
  calc
    (P.comp (Polynomial.X + Polynomial.C (m : ℚ))).eval (n : ℚ) =
        P.eval ((m + n : ℕ) : ℚ) := by simp [Nat.cast_add, add_comm]
    _ = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (Tensor.ProductSheaf.tensorModule M (L.tensorPower (m + n)).sheaf) : ℚ) := hP (m + n)
    _ = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p
        (Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule M (L.tensorPower m).sheaf) (L.tensorPower n).sheaf) : ℚ) :=
      congrArg (fun z : ℤ => (z : ℚ))
        (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso p (coherentTwistShiftIso L M m n)).symm

theorem HasCoherentTwistEulerPolynomial.power
    {p : X ⟶ Spec (.of K)} {M : X.Modules} {L : Line.Bundles.LineBundle X} {P : Polynomial ℚ}
    (hP : HasCoherentTwistEulerPolynomial p M L P) (d : ℕ) :
    HasCoherentTwistEulerPolynomial p M (L.tensorPower d)
      (P.comp (Polynomial.C (d : ℚ) * Polynomial.X)) := by
  intro n
  calc
    (P.comp (Polynomial.C (d : ℚ) * Polynomial.X)).eval (n : ℚ) =
        P.eval ((n * d : ℕ) : ℚ) := by simp [Nat.cast_mul, mul_comm]
    _ = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (Tensor.ProductSheaf.tensorModule M (L.tensorPower (n * d)).sheaf) : ℚ) := hP (n * d)
    _ = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p
        (Tensor.ProductSheaf.tensorModule M ((L.tensorPower d).tensorPower n).sheaf) : ℚ) :=
      congrArg (fun z : ℤ => (z : ℚ))
        (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso p
          (Tensor.Bifunctor.tensorModuleMapIso (Iso.refl M) (L.tensorPowerComposeIso n d)))

theorem lineBundleTwistIteration_quasicoherent (L : Line.Bundles.LineBundle X)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    ((Iterated.EquivalenceCohomology.iterateAutoEquivalence (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L) n).functor.obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (LineBundle.TwistIteration.lineBundleTwistIterationIso L n M).symm (LineBundle.TensorCoherence.tensorModuleRight_lineBundle_quasicoherent M _)

theorem lineBundleTwistIteration_finiteType (L : Line.Bundles.LineBundle X)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) :
    ((Iterated.EquivalenceCohomology.iterateAutoEquivalence (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L) n).functor.obj M).IsFiniteType := by
  have : (Tensor.ProductSheaf.tensorModule M (L.tensorPower n).sheaf).IsQuasicoherent := LineBundle.TensorCoherence.tensorModuleRight_lineBundle_quasicoherent M _
  have : (Tensor.ProductSheaf.tensorModule M (L.tensorPower n).sheaf).IsFiniteType := LineBundle.TensorCoherence.tensorModuleRight_lineBundle_finiteType M _
  have : ((Iterated.EquivalenceCohomology.iterateAutoEquivalence (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L) n).functor.obj M).IsQuasicoherent :=
    lineBundleTwistIteration_quasicoherent L M n
  exact Quasicoherent.RestrictionFiniteType.quasicoherent_finiteType_of_iso (LineBundle.TwistIteration.lineBundleTwistIterationIso L n M).symm

theorem HasCoherentTwistEulerPolynomial.cokernel
    {p : X ⟶ Spec (.of K)} [IsProper p] {M : X.Modules}
    [M.IsQuasicoherent] [M.IsFiniteType] {L : Line.Bundles.LineBundle X} {P : Polynomial ℚ}
    (hP : HasCoherentTwistEulerPolynomial p M L P)
    (s : M ⟶ (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L).functor.obj M) [Mono s] :
    HasCoherentTwistEulerPolynomial p (CategoryTheory.Limits.cokernel s) L (HilbertConstruction.Polynomial.FirstDifference.polynomialFirstDifference P) := by
  let E := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L
  have : (E.functor.obj M).IsQuasicoherent := LineBundle.TensorEquivalenceCoherence.lineBundleRightTensor_quasicoherent L M
  have : (E.functor.obj M).IsFiniteType := LineBundle.TensorEquivalenceCoherence.lineBundleRightTensor_finiteType L M
  have : (CategoryTheory.Limits.cokernel s).IsQuasicoherent := Quasicoherent.Cokernels.module_quasicoherent_cokernel s
  have : (CategoryTheory.Limits.cokernel s).IsFiniteType := Quasicoherent.QuotientFiniteType.quasicoherent_cokernel_finiteType s
  have hpoly (m : ℕ) : P.eval (m : ℚ) =
      (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((Iterated.EquivalenceCohomology.iterateAutoEquivalence E m).functor.obj M) : ℚ) :=
    (hP m).trans (congrArg (fun z : ℤ => (z : ℚ)) (LineBundle.TwistIteration.lineBundleTwistIteration_euler p L M m)).symm
  intro m
  let F := (Iterated.EquivalenceCohomology.iterateAutoEquivalence E m).functor
  have : (F.obj M).IsQuasicoherent := lineBundleTwistIteration_quasicoherent L M m
  have : (F.obj M).IsFiniteType := lineBundleTwistIteration_finiteType L M m
  have : (F.obj (E.functor.obj M)).IsQuasicoherent := lineBundleTwistIteration_quasicoherent L _ m
  have : (F.obj (E.functor.obj M)).IsFiniteType := lineBundleTwistIteration_finiteType L _ m
  have : (F.obj (CategoryTheory.Limits.cokernel s)).IsQuasicoherent := lineBundleTwistIteration_quasicoherent L _ m
  have : (F.obj (CategoryTheory.Limits.cokernel s)).IsFiniteType := lineBundleTwistIteration_finiteType L _ m
  let S : ShortComplex X.Modules := ShortComplex.mk s (cokernel.π s) (cokernel.condition s)
  have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact s⟩
  have : (S.map F).X₁.IsQuasicoherent := inferInstanceAs ((F.obj (M)).IsQuasicoherent)
  have : (S.map F).X₁.IsFiniteType := inferInstanceAs ((F.obj (M)).IsFiniteType)
  have : (S.map F).X₂.IsQuasicoherent := inferInstanceAs ((F.obj (E.functor.obj M)).IsQuasicoherent)
  have : (S.map F).X₂.IsFiniteType := inferInstanceAs ((F.obj (E.functor.obj M)).IsFiniteType)
  have : (S.map F).X₃.IsQuasicoherent := inferInstanceAs ((F.obj (CategoryTheory.Limits.cokernel s)).IsQuasicoherent)
  have : (S.map F).X₃.IsFiniteType := inferInstanceAs ((F.obj (CategoryTheory.Limits.cokernel s)).IsFiniteType)
  have heuler := Proper.CohomologyEulerAdditivity.proper_coherent_euler_additive p (hS.map_of_exact F)
  change CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((Iterated.EquivalenceCohomology.iterateAutoEquivalence E (m + 1)).functor.obj M) =
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj M) + CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj (CategoryTheory.Limits.cokernel s)) at heuler
  have hdifference : CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj (CategoryTheory.Limits.cokernel s)) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((Iterated.EquivalenceCohomology.iterateAutoEquivalence E (m + 1)).functor.obj M) -
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj M) := by omega
  have he : (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj (CategoryTheory.Limits.cokernel s)) : ℚ) =
      P.eval ((m + 1 : ℕ) : ℚ) - P.eval (m : ℚ) := by
    rw [hdifference, Int.cast_sub, ← hpoly (m + 1), ← hpoly m]
  calc
    (HilbertConstruction.Polynomial.FirstDifference.polynomialFirstDifference P).eval (m : ℚ) =
        (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj (CategoryTheory.Limits.cokernel s)) : ℚ) := by
      rw [HilbertConstruction.Polynomial.FirstDifference.polynomialFirstDifference_eval]
      simpa only [Nat.cast_add, Nat.cast_one] using he.symm
    _ = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p
        (Tensor.ProductSheaf.tensorModule (CategoryTheory.Limits.cokernel s) (L.tensorPower m).sheaf) : ℚ) :=
      congrArg (fun z : ℤ => (z : ℚ)) (LineBundle.TwistIteration.lineBundleTwistIteration_euler p L (CategoryTheory.Limits.cokernel s) m)

theorem HasCoherentTwistEulerPolynomial.isZero_of_polynomial_zero
    {p : X ⟶ Spec (.of K)} [IsProper p] {M : X.Modules}
    [M.IsQuasicoherent] [M.IsFiniteType] {L : Line.Bundles.LineBundle X}
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p) (hP : HasCoherentTwistEulerPolynomial p M L 0) : IsZero M := by
  apply E.coherent_isZero_of_twist_euler_zero p M
  intro m
  apply Int.cast_injective (α := ℚ)
  simpa only [Polynomial.eval_zero, Int.cast_zero] using (hP m).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.TwistEulerPolynomial
