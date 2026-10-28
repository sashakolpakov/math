import OAI.RepresentationTheory.Theta.Geometric.CompactAnalyticImage
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.Jacobian

/-! # Critical Image -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CriticalImage

noncomputable section

/-! The critical image of an injective holomorphic map has local analytic
equations and contains no neighborhood of an interior image point. -/

set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped _root_.Topology

variable {n : ℕ} {f : (Fin n → ℂ) → (Fin n → ℂ)} {U K : Set (Fin n → ℂ)}

def holomorphicCriticalPiece (f : (Fin n → ℂ) → (Fin n → ℂ)) (K : Set (Fin n → ℂ)) :=
  K ∩ {x | Jacobian.holomorphicJacobian f x = 0}

theorem holomorphicCriticalPiece_isCompact (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hK : IsCompact K) (hKU : K ⊆ U) : IsCompact (holomorphicCriticalPiece f K) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun x : K => Jacobian.holomorphicJacobian f x) :=
    continuousOn_iff_continuous_domRestrict.mp ((Jacobian.holomorphicJacobian_differentiableOn hU hf).continuousOn.mono hKU)
  have hclosed : IsClosed {x : K | Jacobian.holomorphicJacobian f x = 0} := isClosed_eq hc continuous_const
  have heq : Subtype.val '' {x : K | Jacobian.holomorphicJacobian f x = 0} = holomorphicCriticalPiece f K := by
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.property, hx⟩
    · rintro ⟨hx, hg⟩
      exact ⟨⟨x, hx⟩, hg, rfl⟩
  rw [← heq]
  exact hclosed.isCompact.image continuous_subtype_val

theorem holomorphicCriticalImage_local (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) (hK : IsCompact K) (hKU : K ⊆ U)
    {x : Fin n → ℂ} (hx : x ∈ K) (hxK : K ∈ 𝓝 x) :
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (f '' holomorphicCriticalPiece f K) (f x) := by
  have hSU : holomorphicCriticalPiece f K ⊆ U := fun _ hz => hKU hz.1
  apply CompactAnalyticImage.compact_holomorphic_analytic_image_local hU hf (holomorphicCriticalPiece_isCompact hU hf hK hKU)
    hSU (f x)
  · have hsub : ({z | z ∈ holomorphicCriticalPiece f K ∧ f z = f x} : Set (Fin n → ℂ)).Subsingleton :=
      fun _ hz _ hw => hinj (hSU hz.1) (hSU hw.1) (hz.2.trans hw.2.symm)
    exact hsub.finite
  · intro z hz hzx
    have he : z = x := hinj (hSU hz) (hKU hx) hzx
    subst z
    apply (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticSetOperations.Constructions.Cone.holomorphicZeroSetAt_zero_fiber hU (Jacobian.holomorphicJacobian_differentiableOn hU hf) (hKU hx)).congr
    filter_upwards [hxK] with z hz
    exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

theorem holomorphicCriticalImage_not_mem_nhds (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) (hKU : K ⊆ U) {x : Fin n → ℂ} (hx : x ∈ U) :
    f '' holomorphicCriticalPiece f K ∉ 𝓝 (f x) := by
  intro hnear
  have hfinite (y : Fin n → ℂ) : {z | z ∈ U ∧ f z = y}.Finite := by
    have hsub : ({z | z ∈ U ∧ f z = y} : Set (Fin n → ℂ)).Subsingleton :=
      fun _ hz _ hw => hinj hz.1 hw.1 (hz.2.trans hw.2.symm)
    exact hsub.finite
  apply Jacobian.holomorphicJacobian_not_eventually_zero hU hf hfinite hx
  filter_upwards [hU.mem_nhds hx,
    (hf.differentiableAt (hU.mem_nhds hx)).continuousAt.eventually hnear] with z hz hzimage
  obtain ⟨w, hw, hwz⟩ := hzimage
  have he : w = z := hinj (hKU hw.1) hz hwz
  have hg : Jacobian.holomorphicJacobian f w = 0 := hw.2
  rwa [he] at hg

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CriticalImage
