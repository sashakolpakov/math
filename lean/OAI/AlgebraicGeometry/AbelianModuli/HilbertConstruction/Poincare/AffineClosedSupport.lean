import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AffineParameterSupport
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Affine Closed Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The affine Poincare model is supported on the actual closed inverse image of the dual zero section, without enlarging it by closure. If that inverse image is empty, all its cohomology vanishes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S T : Scheme.{u}} [IsAffine T] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
variable (D : Dual.Data.DualAbelianData A) (t : T ⟶ D.abelian.scheme.left)

theorem Dual.Data.DualAbelianData.dualZeroSection_range_isClosed : IsClosed (Set.range η[D.abelian.scheme].left) := by
  let z := η[D.abelian.scheme].left
  have : IsProper D.abelian.scheme.hom := D.abelian.proper
  have hz : z ≫ D.abelian.scheme.hom = 𝟙 S := η[D.abelian.scheme].w
  have : IsClosedImmersion (z ≫ D.abelian.scheme.hom) := by rw [hz]; exact MorphismProperty.id_mem (@IsClosedImmersion : MorphismProperty Scheme.{u}) S
  have : IsClosedImmersion z := IsClosedImmersion.of_comp (f := z) (g := D.abelian.scheme.hom)
  exact z.isClosedEmbedding.isClosed_range

theorem Dual.Data.DualAbelianData.poincareAffineParameterIdeal_zeroLocus :
    PrimeSpectrum.zeroLocus (D.poincareAffineParameterIdeal t : Set Γ(T, ⊤)) =
      T.isoSpec.hom '' (t ⁻¹' Set.range η[D.abelian.scheme].left) := by
  have hZ : IsClosed (t ⁻¹' Set.range η[D.abelian.scheme].left) :=
    D.dualZeroSection_range_isClosed.preimage t.continuous
  have hi : IsClosed (T.isoSpec.hom '' (t ⁻¹' Set.range η[D.abelian.scheme].left)) :=
    T.isoSpec.hom.homeomorph.isClosedMap _ hZ
  exact (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _).trans hi.closure_eq

variable {P : Scheme.{u}} [P.IsSeparated]
variable {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ T}
variable (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) t)
variable {κ : Type u} [LinearOrder κ] [Finite κ] (U : κ → P.Opens)
variable (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
variable (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj
  (D.poincare.pullback a).sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
variable {C : CochainComplex (ModuleCat.{u} Γ(T, ⊤)) ℕ}
variable (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex b.appTop.hom (D.poincare.pullback a).sheaf U)
variable (ht : ∀ (B : Type u) [AddCommGroup B] [Module Γ(T, ⊤) B], QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ))

include H hU ha he ht in
theorem Dual.Data.DualAbelianData.poincareAffine_model_homology_supported_on_zero
    (hfin : ∀ q, Module.Finite Γ(T, ⊤) (C.X q))
    (hflat : ∀ q, Module.Flat Γ(T, ⊤) (C.X q)) (q : ℕ) :
    Module.support Γ(T, ⊤) (C.homology q) ⊆
      T.isoSpec.hom '' (t ⁻¹' Set.range η[D.abelian.scheme].left) := by
  have h := D.poincareAffine_model_homology_support t H U hU ha he φ ht hfin hflat q
  rwa [D.poincareAffineParameterIdeal_zeroLocus t] at h

include H hU ha he ht in
theorem Dual.Data.DualAbelianData.poincareAffine_model_acyclic_off_zero
    (hfin : ∀ q, Module.Finite Γ(T, ⊤) (C.X q))
    (hflat : ∀ q, Module.Flat Γ(T, ⊤) (C.X q))
    (hoff : t ⁻¹' Set.range η[D.abelian.scheme].left = ∅) : C.Acyclic := by
  intro q
  apply (C.exactAt_iff_isZero_homology q).mpr
  have hs := D.poincareAffine_model_homology_supported_on_zero t H U hU ha he φ ht hfin hflat q
  rw [hoff, Set.image_empty, Set.subset_empty_iff] at hs
  have : Subsingleton (C.homology q) :=
    (Module.support_eq_empty_iff (R := Γ(T, ⊤)) (M := C.homology q)).mp hs
  exact ModuleCat.isZero_of_subsingleton _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
