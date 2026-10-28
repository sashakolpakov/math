import OAI.RepresentationTheory.Theta.Geometric.CompactAnalyticImage
import OAI.RepresentationTheory.Theta.Geometric.Finite.HolomorphicImageInterior

/-! # Injective Holomorphic Open -/

namespace OAI.RepresentationTheory.Theta.Geometric.InjectiveHolomorphicOpen

noncomputable section

/-! An injective holomorphic map between finite-dimensional complex spaces
of equal dimension is open on its open domain. -/

open Set Filter _root_.Metric
open scoped _root_.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

theorem injective_holomorphic_image_isOpen
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) :
    IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hfinite (y : F) : {z | z ∈ U ∧ f z = y}.Finite := by
    have hsub : ({z | z ∈ U ∧ f z = y} : Set E).Subsingleton :=
      fun _ hz _ hw => hinj hz.1 hw.1 (hz.2.trans hw.2.symm)
    exact hsub.finite
  have hlocal := CompactAnalyticImage.compact_injective_holomorphic_image_local hU hf (isCompact_closedBall x r)
    hball (hinj.mono hball) (mem_closedBall_self hr.le) (closedBall_mem_nhds x hr)
  exact Filter.mem_of_superset (Geometric.Finite.HolomorphicImageInterior.finite_holomorphic_image_mem_nhds hdim hU hf hfinite hx
    (closedBall_mem_nhds x hr) hlocal) (image_mono hball)

theorem injective_holomorphic_restrict_isOpenMap
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) :
    IsOpenMap (fun x : U => f x) := by
  intro V hV
  have hval : IsOpen (Subtype.val '' V) := hU.isOpenMap_subtype_val V hV
  have hsub : Subtype.val '' V ⊆ U := by rintro x ⟨x, _, rfl⟩; exact x.property
  have h := injective_holomorphic_image_isOpen hdim hval (hf.mono hsub) (hinj.mono hsub)
  simpa only [image_image, Function.comp_def] using h

def injectiveHolomorphicPartialHomeomorph
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) :
    OpenPartialHomeomorph E F :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv f U) hf.continuousOn
    (injective_holomorphic_restrict_isOpenMap hdim hU hf hinj) hU

theorem injectiveHolomorphicPartialHomeomorph_apply
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) :
    (injectiveHolomorphicPartialHomeomorph hdim hU hf hinj : E → F) = f := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.InjectiveHolomorphicOpen
