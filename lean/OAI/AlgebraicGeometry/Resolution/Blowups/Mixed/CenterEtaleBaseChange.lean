import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.EquationCongruence
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ChartEtaleBaseChange

/-! # Center Etale Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual affine pullbacks preserve common coordinates for a center and its divided labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u v

variable {k : Type u} [CommRing k] {R S : CommRingCat.{u}} [Algebra k R] [Algebra k S]
  {ι : Type v} {w : ι → R} {I : Ideal R} {F : Finset ι}

theorem Mixed.CenterEtaleBaseChange.Construction.exists_mixed_center_chart_etale_base_change (f : R →ₐ[k] S)
    (hf : f.toRingHom.Etale) (q : PrimeSpectrum S)
    (C : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F (PrimeSpectrum.comap f.toRingHom q)) :
    Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k S (I.map f.toRingHom) (fun j => f (w j)) F q) := by
  let B := C.chart
  let : Algebra R B.carrier := B.map.toRingHom.toAlgebra
  let : Algebra R S := f.toRingHom.toAlgebra
  let T := B.carrier ⊗[R] S
  let l : B.carrier →+* T := Algebra.TensorProduct.includeLeftRingHom
  let r : S →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let : Algebra k T := (l.comp (algebraMap k B.carrier)).toAlgebra
  have hcomm (x : R) : l (B.map x) = r (f x) := by
    exact congrArg (fun h : R →+* T => h x)
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := R) (A := B.carrier) (B := S))
  let lₖ : B.carrier →ₐ[k] T := { toRingHom := l, commutes' := fun _ => rfl }
  let rₖ : S →ₐ[k] T :=
    { toRingHom := r
      commutes' := fun c => by
        change r (algebraMap k S c) = l (algebraMap k B.carrier c)
        rw [← f.commutes c, ← B.map.commutes c]
        exact (hcomm (algebraMap k R c)).symm }
  have hpb : IsPullback (Spec.map (CommRingCat.ofHom l)) (Spec.map (CommRingCat.ofHom r))
      (Spec.map (CommRingCat.ofHom B.map.toRingHom)) (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    apply isPullback_SpecMap_of_isPushout
    exact CommRingCat.isPushout_tensorProduct R B.carrier S
  have hfe : Etale (Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hf
  have hle : Etale (Spec.map (CommRingCat.ofHom l)) :=
    MorphismProperty.of_isPullback (P := @Etale) hpb.flip hfe
  have hl : lₖ.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp hle
  have hr : IsOpenImmersion (Spec.map (CommRingCat.ofHom r)) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb inferInstance
  obtain ⟨Q, _, hQ⟩ := Scheme.exists_preimage_of_isPullback hpb B.point q B.point_over
  let N := (B.model.baseChange lₖ hl).congrEquations (fun j => rₖ (f (w j)))
    (fun j => (hcomm (w j)).symm)
  let O : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k S (fun j => f (w j)) q :=
    { carrier := .of T
      algebra := inferInstance
      map := rₖ
      isOpenImmersion := hr
      point := Q
      point_over := hQ
      model := N }
  refine ⟨{ chart := O
            coordinates := C.coordinates
            center_eq := ?_
            divided_iff := C.divided_iff }⟩
  change (I.map f.toRingHom).map r = (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C.coordinates).map (l.comp B.model.map)
  have hcommHom : l.comp B.map.toRingHom = r.comp f.toRingHom := RingHom.ext hcomm
  rw [Ideal.map_map, ← hcommHom, ← Ideal.map_map, C.center_eq, Ideal.map_map]

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.etale_baseChange
    (h : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F) (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k S (I.map f.toRingHom) (fun j => f (w j)) F := by
  intro q hq
  have hp : I ≤ (PrimeSpectrum.comap f.toRingHom q).asIdeal :=
    Ideal.map_le_iff_le_comap.mp hq
  obtain ⟨C⟩ := h (PrimeSpectrum.comap f.toRingHom q) hp
  exact Mixed.CenterEtaleBaseChange.Construction.exists_mixed_center_chart_etale_base_change f hf q C

end

end OAI.AlgebraicGeometry.Resolution.Blowups
