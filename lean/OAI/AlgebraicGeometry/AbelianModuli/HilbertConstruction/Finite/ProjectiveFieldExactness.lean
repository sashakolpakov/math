import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LocalizationExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ResidueExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.TensorExactness
import Mathlib.RingTheory.Flat.Localization

/-! # Projective Field Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveFieldExactness

noncomputable section

/-! A short complex of finite projective modules that is exact after
all field-valued scalar maps is exact over the original ring and after
every coefficient-ring extension. -/
open _root_.CategoryTheory
open scoped TensorProduct
universe u
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ResidueExactness.LocalSectionLifting
variable {R : Type u} [CommRing R]
variable (C : ShortComplex (ModuleCat.{u} R))
variable [Module.Finite R C.X₁] [Module.Projective R C.X₁]
variable [Module.Finite R C.X₂] [Module.Projective R C.X₂]
variable [Module.Finite R C.X₃] [Module.Projective R C.X₃]

theorem finiteProjectiveShortComplex_exact_of_field_tests
    (h : ∀ (K : Type u) [Field K] (q : R →+* K),
      (C.map (ModuleCat.extendScalars q)).Exact) : C.Exact := by
  apply Tensor.LocalizationExactness.shortComplex_exact_of_tensor_localizations C
  intro I _
  let A := Localization.AtPrime I
  let T := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R A C
  have : Module.Finite A T.X₁ := inferInstanceAs (Module.Finite A (A ⊗[R] C.X₁))
  have : Module.Finite A T.X₂ := inferInstanceAs (Module.Finite A (A ⊗[R] C.X₂))
  have : Module.Finite A T.X₃ := inferInstanceAs (Module.Finite A (A ⊗[R] C.X₃))
  have : Module.Flat A T.X₁ := inferInstanceAs (Module.Flat A (A ⊗[R] C.X₁))
  have : Module.Flat A T.X₂ := inferInstanceAs (Module.Flat A (A ⊗[R] C.X₂))
  have : Module.Flat A T.X₃ := inferInstanceAs (Module.Flat A (A ⊗[R] C.X₃))
  have : Module.Free A T.X₁ := Module.free_of_flat_of_isLocalRing
  have : Module.Free A T.X₂ := Module.free_of_flat_of_isLocalRing
  have : Module.Free A T.X₃ := Module.free_of_flat_of_isLocalRing
  apply Local.ResidueExactness.LocalSectionLifting.finiteFreeShortComplex_exact_of_residue_exact T
  exact (Iterated.TensorExactness.iterated_tensor_exact_iff_composite (A := A)
    (B := IsLocalRing.ResidueField A) C).mpr
      (h (IsLocalRing.ResidueField A)
        ((algebraMap A (IsLocalRing.ResidueField A)).comp (algebraMap R A)))

theorem finiteProjectiveShortComplex_universal_exact_of_field_tests
    (h : ∀ (K : Type u) [Field K] (q : R →+* K),
      (C.map (ModuleCat.extendScalars q)).Exact)
    (B : Type u) [CommRing B] [Algebra R B] :
    (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B C).Exact := by
  let T := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B C
  have : Module.Finite B T.X₁ := inferInstanceAs (Module.Finite B (B ⊗[R] C.X₁))
  have : Module.Finite B T.X₂ := inferInstanceAs (Module.Finite B (B ⊗[R] C.X₂))
  have : Module.Finite B T.X₃ := inferInstanceAs (Module.Finite B (B ⊗[R] C.X₃))
  have : Module.Projective B T.X₁ := inferInstanceAs (Module.Projective B (B ⊗[R] C.X₁))
  have : Module.Projective B T.X₂ := inferInstanceAs (Module.Projective B (B ⊗[R] C.X₂))
  have : Module.Projective B T.X₃ := inferInstanceAs (Module.Projective B (B ⊗[R] C.X₃))
  apply finiteProjectiveShortComplex_exact_of_field_tests T
  intro K _ q
  let : Algebra B K := q.toAlgebra
  have hi : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex B K T).Exact :=
    (Iterated.TensorExactness.iterated_tensor_exact_iff_composite (A := B) (B := K) C).mpr
      (h K (q.comp (algebraMap R B)))
  exact (ShortComplex.exact_iff_of_iso
    (T.mapNatIso (Scalar.FunctorComparison.ScalarFunctorComparison.isoOfHom B K q))).mp hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveFieldExactness
