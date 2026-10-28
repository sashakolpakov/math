import OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryProperty
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Chart Etale Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual affine pullbacks of pointed boundary charts along étale refinement maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u v

variable {k : Type u} [CommRing k] {R S : CommRingCat.{u}} [Algebra k R] [Algebra k S]
  {ι : Type v} {w : ι → R}

/-- Pulling a source boundary chart back by an étale map gives an actual
open chart through the chosen target prime, with the original equations
pulled back by that map and the ground algebra unchanged. -/
theorem Boundary.ChartEtaleBaseChange.Construction.exists_boundary_open_chart_etale_base_change (f : R →ₐ[k] S)
    (hf : f.toRingHom.Etale) (q : PrimeSpectrum S)
    (C : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R w (PrimeSpectrum.comap f.toRingHom q)) :
    Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k S (fun j => f (w j)) q) := by
  let : Algebra R C.carrier := C.map.toRingHom.toAlgebra
  let : Algebra R S := f.toRingHom.toAlgebra
  let T := C.carrier ⊗[R] S
  let l : C.carrier →+* T := Algebra.TensorProduct.includeLeftRingHom
  let r : S →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let : Algebra k T := (l.comp (algebraMap k C.carrier)).toAlgebra
  have hcomm (x : R) : l (C.map x) = r (f x) := by
    exact congrArg (fun h : R →+* T => h x)
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := R) (A := C.carrier) (B := S))
  let lₖ : C.carrier →ₐ[k] T := { toRingHom := l, commutes' := fun _ => rfl }
  let rₖ : S →ₐ[k] T :=
    { toRingHom := r
      commutes' := fun c => by
        change r (algebraMap k S c) = l (algebraMap k C.carrier c)
        rw [← f.commutes c, ← C.map.commutes c]
        exact (hcomm (algebraMap k R c)).symm }
  have hpb : IsPullback (Spec.map (CommRingCat.ofHom l)) (Spec.map (CommRingCat.ofHom r))
      (Spec.map (CommRingCat.ofHom C.map.toRingHom)) (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    apply isPullback_SpecMap_of_isPushout
    exact CommRingCat.isPushout_tensorProduct R C.carrier S
  have hfe : Etale (Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hf
  have hle : Etale (Spec.map (CommRingCat.ofHom l)) :=
    MorphismProperty.of_isPullback (P := @Etale) hpb.flip hfe
  have hl : lₖ.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp hle
  have hr : IsOpenImmersion (Spec.map (CommRingCat.ofHom r)) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb inferInstance
  obtain ⟨Q, _, hQ⟩ := Scheme.exists_preimage_of_isPullback hpb C.point q C.point_over
  refine ⟨{ carrier := .of T
            algebra := inferInstance
            map := rₖ
            isOpenImmersion := hr
            point := Q
            point_over := hQ
            model := ?_ }⟩
  have he : (fun j => rₖ (f (w j))) = (fun j => lₖ (C.map (w j))) := by
    funext j
    exact (hcomm (w j)).symm
  rw [he]
  exact C.model.baseChange lₖ hl

/-- The local property is stable under every actual étale algebra map. -/
theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.etale_baseChange (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w)
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k S (fun j => f (w j)) := by
  intro q
  obtain ⟨C⟩ := h (PrimeSpectrum.comap f.toRingHom q)
  exact Boundary.ChartEtaleBaseChange.Construction.exists_boundary_open_chart_etale_base_change f hf q C

end

end OAI.AlgebraicGeometry.Resolution.Blowups
