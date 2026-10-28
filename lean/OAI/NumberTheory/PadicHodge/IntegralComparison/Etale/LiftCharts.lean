import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.StandardEtaleCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.StandardEtaleLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentAffineSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentOpenRestriction

/-! # Lift Charts -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftCharts

noncomputable section

/-! Actual standard-etale charts lifted over a nilpotent closed
thickening of the target. The reduced charts cover the original source,
and the maps to both original schemes retain their literal triangles. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X X₀ Y₀ : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker) (f : Y₀ ⟶ X₀) [Etale f] [IsAffineHom f]

abbrev baseCover : X₀.OpenCover where
  I₀ := X.affineOpens
  X U := (i ⁻¹ᵁ U.1).toScheme
  f U := (i ⁻¹ᵁ U.1).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    have hx : i x ∈ ⨆ U : X.affineOpens, U.1 := (iSup_affineOpens_eq_top X).symm ▸ trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U, ⟨⟨x, hU⟩, rfl⟩⟩

instance baseCover_affine (U : (baseCover i).I₀) : IsAffine ((baseCover i).X U) := U.2.preimage i

abbrev Index := Relative.StandardEtaleCover.Index f (baseCover i)
abbrev thickRing (U : X.affineOpens) : CommRingCat.{u} := Γ(U.1.toScheme, ⊤)
abbrev residueRing (U : X.affineOpens) : CommRingCat.{u} := Γ((i ⁻¹ᵁ U.1).toScheme, ⊤)

instance thick_affine (U : X.affineOpens) : IsAffine U.1.toScheme := U.2
instance residue_affine (U : X.affineOpens) : IsAffine (i ⁻¹ᵁ U.1).toScheme := U.2.preimage i
instance residueAlgebra (U : X.affineOpens) : Algebra (thickRing U) (residueRing i U) :=
  (i ∣_ U.1).appTop.hom.toAlgebra

theorem coefficient_surjective (U : X.affineOpens) :
    Function.Surjective (algebraMap (thickRing U) (residueRing i U)) := by
  change Function.Surjective (i ∣_ U.1).appTop
  simpa [Scheme.Hom.appTop] using (i ∣_ U.1).app_surjective ⊤ (isAffineOpen_top U.1.toScheme)

include hi in
theorem coefficient_nilpotent (U : X.affineOpens) :
    IsNilpotent (RingHom.ker (algebraMap (thickRing U) (residueRing i U))) :=
  NilpotentAffineSections.appTop (i ∣_ U.1)
    (NilpotentOpenRestriction.nilpotent i hi U.1)

abbrev pair (a : Index i f) : StandardEtalePair (residueRing i a.1) := by
  letI := Relative.StandardEtaleCover.coordinateAlgebra f (baseCover i) a
  exact (Relative.StandardEtaleCover.presentation f (baseCover i) a).P

abbrev chartRing (a : Index i f) : Type u :=
  Finite.StandardEtaleLift.Ring (thickRing a.1) (residueRing i a.1)
    (coefficient_surjective i a.1) (pair i f a)

abbrev chart (a : Index i f) : Scheme.{u} := Spec (.of (chartRing i f a))
abbrev reducedChart (a : Index i f) : Scheme.{u} := Spec (.of (pair i f a).Ring)

def reduction (a : Index i f) : reducedChart i f a ⟶ chart i f a :=
  Spec.map (CommRingCat.ofHom (Finite.StandardEtaleLift.reduction
    (thickRing a.1) (residueRing i a.1) (coefficient_surjective i a.1) (pair i f a)))

instance reduction_closed (a : Index i f) : IsClosedImmersion (reduction i f a) :=
  Finite.StandardEtaleLift.reduction_closed _ _ _ _

include hi in
theorem reduction_nilpotent (a : Index i f) : IsNilpotent (reduction i f a).ker :=
  NilpotentAffineSections.spec _
    (Finite.StandardEtaleLift.kernel_nilpotent _ _ _ _ (coefficient_nilpotent i hi a.1))

include hi in
theorem reduction_surjective (a : Index i f) : Surjective (reduction i f a) :=
  Finite.StandardEtaleLift.reduction_surjective _ _ _ _ (coefficient_nilpotent i hi a.1)

def reductionHomeomorph (a : Index i f) : reducedChart i f a ≃ₜ chart i f a :=
  Finite.StandardEtaleLift.reductionHomeomorph _ _ _ _ (coefficient_nilpotent i hi a.1)

def sourceMap (a : Index i f) : reducedChart i f a ⟶ Y₀ :=
  Relative.StandardEtaleCover.presentedMap f (baseCover i) a

instance sourceMap_open (a : Index i f) : IsOpenImmersion (sourceMap i f a) :=
  Relative.StandardEtaleCover.presentedMap_open f (baseCover i) a

theorem sourceMap_covers (y : Y₀) : ∃ a : Index i f, y ∈ Set.range (sourceMap i f a) :=
  Relative.StandardEtaleCover.presented_covers f (baseCover i) y

def chartBase (a : Index i f) : chart i f a ⟶ a.1.1.toScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap (thickRing a.1) (chartRing i f a))) ≫
    a.1.1.toScheme.isoSpec.inv

instance chartBase_etale (a : Index i f) : Etale (chartBase i f a) := by
  let : Algebra.Etale (thickRing a.1) (chartRing i f a) :=
    StandardEtaleLiftAlgebra.etale _ _ _
  let : Etale (Spec.map (CommRingCat.ofHom (algebraMap (thickRing a.1) (chartRing i f a)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  unfold chartBase
  infer_instance

def chartMap (a : Index i f) : chart i f a ⟶ X := chartBase i f a ≫ a.1.1.ι

instance chartMap_etale (a : Index i f) : Etale (chartMap i f a) := by
  unfold chartMap
  infer_instance

theorem reduction_over (a : Index i f) : reduction i f a ≫ chartMap i f a = sourceMap i f a ≫ f ≫ i := by
  rw [chartMap, chartBase, reduction, ← Category.assoc, ← Category.assoc]
  rw [(Finite.StandardEtaleLift.square (thickRing a.1) (residueRing i a.1)
    (coefficient_surjective i a.1) (pair i f a)).w]
  simp only [Category.assoc]
  change Spec.map (CommRingCat.ofHom (algebraMap (residueRing i a.1) (pair i f a).Ring)) ≫
    Spec.map (i ∣_ a.1.1).appTop ≫ a.1.1.toScheme.isoSpec.inv ≫ a.1.1.ι = _
  rw [Scheme.isoSpec_inv_naturality_assoc]
  rw [morphismRestrict_ι]
  have h := congrArg (fun q : reducedChart i f a ⟶ X₀ => q ≫ i)
    (Relative.StandardEtaleCover.presentedMap_over f (baseCover i) a).symm
  dsimp only [pair, Relative.StandardEtaleCover.baseRing, baseCover, residueRing,
    sourceMap, reducedChart] at h ⊢
  simpa only [Category.assoc] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftCharts
