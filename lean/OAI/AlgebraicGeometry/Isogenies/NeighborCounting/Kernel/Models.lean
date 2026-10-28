import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base

/-! # Models -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models

noncomputable section

/-!
Finite locally free models of the complete multiplier-level kernels.
The only annihilator-model input is the finite-flat representability clause
of CartierDuality for the actual paired torsion blocks. Products and embeddings are
constructed, including in characteristic q; no etaleness of q-torsion is used.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]

omit [IsCommMonObj A] in
theorem killedBy_of_dvd {m n : ℕ} (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (hF : F.KilledBy m) (hmn : m ∣ n) : F.KilledBy n := by
  obtain ⟨k, rfl⟩ := hmn
  intro X t x hx
  rw [pow_mul, hF X t x hx, one_pow]

omit [IsCommMonObj A] in
theorem active_q_kernel_killed_at_multiplier (q i : ℕ) (hi : 0 < i)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (hF : F.KilledBy q) : F.KilledBy (q ^ i) :=
  killedBy_of_dvd F hF (dvd_pow_self q (Nat.ne_of_gt hi))

variable (n : ℕ) (p q : A ⟶ A) [IsMonHom p] [IsMonHom q]
variable {W : Over S} [GrpObj W]
variable (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p) (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n q) (W := W))

/-- This is exactly the representability clause supplied by perfect finite
flat Cartier duality on the fixed paired blocks, for all finite flat subgroups. -/
def AnnihilatorModelInput : Prop :=
  ∀ (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p) P),
    Nonempty F.Model → Nonempty (e.relativeAnnihilator F).Model

/-- CartierDuality supplies the opposite model; the complete pair is then built as
the fiber product, with monicity proved from the separating projector. -/
theorem opposite_and_pair_models_of_CartierDuality
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model)
    (hkilled : F.KilledBy n) (hsupport : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn F p)
    (hpq : AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n p = 1)
    (h_CartierDuality : AnnihilatorModelInput (P := P) n p q e) :
    Nonempty (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n p q e F).Model ∧
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n p q e F).KilledBy n ∧
      Nonempty (AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct F (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n p q e F)).Model ∧
      (AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct F (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n p q e F)).KilledBy n := by
  let FB := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p) F
  let RB := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.supportedTorsionBlock_model n p F R hkilled hsupport
  obtain ⟨Q⟩ := h_CartierDuality FB ⟨RB⟩
  let G := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n p q e F
  let RG : G.Model := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage_model (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n q)
    (e.relativeAnnihilator FB) Q
  have hGkilled : G.KilledBy n := by
    intro X t x hx
    obtain ⟨y, _, rfl⟩ := hx
    change (y ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n q) ^ n = 1
    rw [← MonObj.comp_pow, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.comp_one]
  have hRG : RG.toGroup ≫ p = 1 := by
    change (Q.toGroup ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n q) ≫ p = 1
    rw [Category.assoc, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_separated n p q hpq, MonObj.comp_one]
  refine ⟨⟨RG⟩, hGkilled, ?_, AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct_killed F G n hkilled hGkilled⟩
  exact ⟨AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct_model F G R RG p
    ((AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedOn_iff_model_equation F R p).mp hsupport) hRG⟩

/-- Actual torsion and projector equations give separation from every
other block on all test schemes, including nonreduced tests. -/
theorem supported_kernel_annihilated
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (hkilled : F.KilledBy n)
    (hsupport : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn F q)
    (hpq : AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n p = 1) : AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy F p := by
  intro X t x hx
  rw [← AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift_inclusion n q x (hkilled X t x hx) (hsupport X t x hx),
    Category.assoc, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_separated n p q hpq, MonObj.comp_one]

variable {s : ℕ} (chosenProjector oppositeProjector : Fin s → (A ⟶ A))
variable [∀ v, IsMonHom (chosenProjector v)] [∀ v, IsMonHom (oppositeProjector v)]
variable (pairing : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
  (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (chosenProjector v)) (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (oppositeProjector v)) (W := W))

/-- The multiplier parameter occurs in the literal scheme-theoretic torsion
blocks. The active input is still the original q-torsion subgroup. -/
def multiplierFullKernel (active : Fin s) (multiplicative : Fin s → Bool)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P :=
  Base.fullKernel (fun v => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (chosenProjector v))
    (fun v => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (oppositeProjector v))
    (fun v => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (chosenProjector v))
    (fun v => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (oppositeProjector v)) pairing active multiplicative F

theorem multiplier_chosenKernel_killed
    (active : Fin s) (multiplicative : Fin s → Bool)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (hF : F.KilledBy n) (v : Fin s) :
    (Base.chosenKernel (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (chosenProjector w))
      (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (chosenProjector w)) active multiplicative F v).KilledBy n := by
  classical
  unfold Base.chosenKernel
  split_ifs
  · exact hF
  · intro X t x hx
    obtain ⟨y, rfl⟩ := hx
    change (y ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (chosenProjector v)) ^ n = 1
    rw [← MonObj.comp_pow, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.comp_one]
  · intro X t x hx
    change x = 1 at hx
    rw [hx, one_pow]

def multiplier_chosenKernel_model
    [∀ v, IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (chosenProjector v)).hom]
    [∀ v, Flat (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (chosenProjector v)).hom]
    [∀ v, LocallyOfFinitePresentation (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (chosenProjector v)).hom]
    (active : Fin s) (multiplicative : Fin s → Bool)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) (v : Fin s) :
    (Base.chosenKernel (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (chosenProjector w))
      (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (chosenProjector w)) active multiplicative F v).Model := by
  classical
  unfold Base.chosenKernel
  split_ifs
  · exact R
  · exact Base.fixedKernelFamily_model _
  · exact AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup_model

theorem multiplier_chosenKernel_supported
    (active : Fin s) (multiplicative : Fin s → Bool)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (hF : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn F (chosenProjector active)) (v : Fin s) :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (Base.chosenKernel (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (chosenProjector w))
      (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (chosenProjector w)) active multiplicative F v)
      (chosenProjector v) := by
  classical
  unfold Base.chosenKernel
  split_ifs with hv
  · subst v
    exact hF
  · intro X t x hx
    obtain ⟨y, rfl⟩ := hx
    change (y ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (chosenProjector v)) ≫ chosenProjector v = _
    rw [Category.assoc, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_supported]
    rfl
  · intro X t x hx
    change x = 1 at hx
    rw [hx, MonObj.one_comp]

theorem oppositeKernel_supported (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n p q e F) q := by
  intro X t x hx
  obtain ⟨y, _, rfl⟩ := hx
  change (y ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n q) ≫ q = _
  rw [Category.assoc, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_supported]
  rfl

theorem oppositeKernel_killed (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n p q e F).KilledBy n := by
  intro X t x hx
  obtain ⟨y, _, rfl⟩ := hx
  change (y ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n q) ^ n = 1
  rw [← MonObj.comp_pow, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.comp_one]

instance sumProjector_isMonHom (p q : A ⟶ A) [IsMonHom p] [IsMonHom q] :
    IsMonHom (p * q) := by
  change IsMonHom (lift p q ≫ μ[A])
  infer_instance

/-- Assemble all paired kernels as a finite locally free subgroup. Only
the individual CartierDuality annihilator model is supplied; the product model and
all joint monomorphisms are constructed using the split projectors. -/
def multiplierFullKernel_model
    [∀ v, IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (chosenProjector v)).hom]
    [∀ v, Flat (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (chosenProjector v)).hom]
    [∀ v, LocallyOfFinitePresentation (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (chosenProjector v)).hom]
    (active : Fin s) (multiplicative : Fin s → Bool)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model)
    (hF : F.KilledBy n) (hFs : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn F (chosenProjector active))
    (hcc : ∀ v w, v ≠ w → AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (chosenProjector w) ≫
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (chosenProjector v) = 1)
    (hoc : ∀ v w, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (oppositeProjector w) ≫
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (chosenProjector v) = 1)
    (hco : ∀ v w, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (chosenProjector w) ≫
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (oppositeProjector v) = 1)
    (hoo : ∀ v w, v ≠ w → AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (oppositeProjector w) ≫
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n (oppositeProjector v) = 1)
    (h_CartierDuality : ∀ v, AnnihilatorModelInput (P := P) n (chosenProjector v)
      (oppositeProjector v) (pairing v)) :
    (multiplierFullKernel n chosenProjector oppositeProjector pairing active multiplicative F).Model := by
  let chosen := fun v => Base.chosenKernel (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (chosenProjector w))
    (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (chosenProjector w)) active multiplicative F v
  let opposite := fun v => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n (chosenProjector v) (oppositeProjector v) (pairing v) (chosen v)
  let pair := fun v => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (chosen v) (opposite v)
  let totalProjector := fun v => chosenProjector v * oppositeProjector v
  have hcK (v : Fin s) : (chosen v).KilledBy n :=
    multiplier_chosenKernel_killed n chosenProjector active multiplicative F hF v
  have hcS (v : Fin s) : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (chosen v) (chosenProjector v) :=
    multiplier_chosenKernel_supported n chosenProjector active multiplicative F hFs v
  have hoK (v : Fin s) : (opposite v).KilledBy n :=
    oppositeKernel_killed n _ _ _ _
  have hoS (v : Fin s) : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (opposite v) (oppositeProjector v) :=
    oppositeKernel_supported n _ _ _ _
  have hcO (v w : Fin s) : AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy (chosen w) (oppositeProjector v) :=
    supported_kernel_annihilated n _ _ (chosen w) (hcK w) (hcS w) (hco v w)
  have hoC (v w : Fin s) : AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy (opposite w) (chosenProjector v) :=
    supported_kernel_annihilated n _ _ (opposite w) (hoK w) (hoS w) (hoc v w)
  have hcC (v w : Fin s) (hvw : v ≠ w) : AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy (chosen w) (chosenProjector v) :=
    supported_kernel_annihilated n _ _ (chosen w) (hcK w) (hcS w) (hcc v w hvw)
  have hoO (v w : Fin s) (hvw : v ≠ w) : AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy (opposite w) (oppositeProjector v) :=
    supported_kernel_annihilated n _ _ (opposite w) (hoK w) (hoS w) (hoo v w hvw)
  let model : ∀ v, (pair v).Model := fun v =>
    (opposite_and_pair_models_of_CartierDuality n (chosenProjector v) (oppositeProjector v) (pairing v)
      (chosen v) (multiplier_chosenKernel_model n chosenProjector active multiplicative F R v)
      (hcK v) (hcS v) (hoc v v) (h_CartierDuality v)).2.2.1.some
  have pairS (v : Fin s) : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (pair v) (totalProjector v) := by
    intro X t z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    change (x * y) ≫ (chosenProjector v * oppositeProjector v) = x * y
    rw [MonObj.mul_comp, MonObj.comp_mul, MonObj.comp_mul,
      hcS v X t x hx, hcO v v X t x hx, hoC v v X t y hy, hoS v X t y hy,
      mul_one, one_mul]
  have pairA (v w : Fin s) (hvw : v ≠ w) : AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy (pair w) (totalProjector v) := by
    intro X t z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    change (x * y) ≫ (chosenProjector v * oppositeProjector v) = 1
    rw [MonObj.mul_comp, MonObj.comp_mul, MonObj.comp_mul,
      hcC v w hvw X t x hx, hcO v w X t x hx,
      hoC v w X t y hy, hoO v w hvw X t y hy, one_mul, one_mul]
  exact AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel_model s pair model totalProjector
    (fun v => (AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedOn_iff_model_equation _ (model v) _).mp (pairS v))
    (fun v w hvw => (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.annihilatedBy_iff_model_equation _ (model w) _).mp (pairA v w hvw))

theorem multiplierFullKernel_killed
    (active : Fin s) (multiplicative : Fin s → Bool)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (hF : F.KilledBy n) :
    (multiplierFullKernel n chosenProjector oppositeProjector pairing active multiplicative F).KilledBy n := by
  apply AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel_killed
  intro v
  apply AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct_killed
  · exact multiplier_chosenKernel_killed n chosenProjector active multiplicative F hF v
  · intro X t x hx
    obtain ⟨y, _, rfl⟩ := hx
    change (y ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (oppositeProjector v)) ^ n = 1
    rw [← MonObj.comp_pow, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.comp_one]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models
