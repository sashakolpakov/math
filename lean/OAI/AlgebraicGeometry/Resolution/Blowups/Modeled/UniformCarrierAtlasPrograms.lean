import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.UniformCarrierAtlasProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.OrderCoverProgramGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.UniformCoefficientCarrierPrograms
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.CompatibilityOrderComplement

/-! # Uniform Carrier Atlas Programs -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.UniformCarrierAtlasPrograms.Construction

noncomputable section

section

/-! Actual normal-chart programs glue to a global program retaining all their coefficient certificates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_glued_modeled_uniform_carrier_atlas_program {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥) (n : ℕ)
    {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι] [Nonempty ι]
    (D : β → X.IdealSheafData) (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ])
    (x : ι → X) (C : ∀ i, GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D (x i))
    [∀ i, IsDomain (C i).chart.ring] [∀ i, IsIntegral (C i).chart.nativeCarrier.subscheme]
    [∀ i, Smooth ((C i).chart.nativeCarrier.subschemeι ≫ ((C i).chart.map ≫ f))]
    (hdH : ∀ i, topologicalKrullDim (C i).chart.nativeCarrier.subscheme ≤ d)
    (hcover : ∀ y ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support, ∃ i p, (C i).chart.map p = y)
    (hC : ∀ i, GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf ((C i).chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap (C i).chart.map) (n + 1)
        (C i).chart.nativeCarrier.subschemeι ≠ ⊥)
    (schedule : 𝒮.Schedule (n + 1).factorial β)
    (Y : ι → Scheme) (g : ∀ i, Y i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : ∀ i, (Y i).IdealSheafData)
    (P : ∀ i, Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (Spec (C i).chart.ring) ((C i).chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap (C i).chart.map) (Y i) (g i) (K i))
    (certificate : ∀ i, Uniform.CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule ((C i).chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap (C i).chart.map) (C i).chart.nativeCarrier
        (fun l => (D l).comap (C i).chart.map) (P i))
    (htrace : ∀ i, (P i).HasIncidenceTrace β (fun l => (D l).comap (C i).chart.map) (𝒮.incidenceTrace schedule))
    (ht : ∀ i, letI : Smooth (g i) := (P i).endpoint_smooth; Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (g i) (K i) n = ⊤) :
    ∃ (Z : Scheme) (h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : Z.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) Z h L),
      Nonempty (UniformCarrierAtlasProgram.Construction.ModeledUniformCarrierAtlasProgram 𝒮 schedule f J D Q) := by
  let : ∀ i, IsNoetherianRing (C i).chart.ring := fun i => Algebra.FiniteType.isNoetherianRing ℂ (C i).chart.ring
  let : ∀ i, IsLocallyNoetherian (Spec (C i).chart.ring) := fun _ => inferInstance
  let : ∀ i, IsIntegral (Spec (C i).chart.ring) := fun _ => inferInstance
  let : ∀ i, CompactSpace (Spec (C i).chart.ring) := fun _ => inferInstance
  have hcompat : ∀ i a, (P i).OpenCompatible (P a) (C i).chart.map (C a).chart.map := by
    intro i a
    apply Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.openCompatible_of_order_comparisons f (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n)
      (C i).chart.map (C a).chart.map (P i) (P a)
      ((certificate i).stepCount.trans (certificate a).stepCount.symm)
    intro p q hpq hp
    rw [Global.Homogenization.Construction.smoothHomogenizedIdealSheaf_tangent] at hp
    exact (certificate i).openComparisonAt_of_global_normal_charts (C i) (C a) (certificate a)
      (hC i) (hC a) (hdH i) (hdH a) p q hpq hp
  have hJH : Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n ≠ ⊥ :=
    ne_bot_of_le_ne_bot hJ (Global.Homogenization.Construction.le_smoothHomogenizedIdealSheaf f J n)
  have hcoverH : ∀ y ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) (n + 1 - 1)).support,
      ∃ i p, (C i).chart.map p = y := by
    simpa only [Nat.add_sub_cancel, Global.Homogenization.Construction.smoothHomogenizedIdealSheaf_tangent] using hcover
  have ht' : ∀ i, letI : Smooth (g i) := (P i).endpoint_smooth;
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (g i) (K i) (n + 1 - 1) = ⊤ := by
    simpa only [Nat.add_sub_cancel] using ht
  obtain ⟨Z, h, L, Q, r, hQ, hterm, hr⟩ := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_complete_of_finite_order_cover
    f (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) hJH (n + 1) (fun i => Spec (C i).chart.ring)
    (fun i => (C i).chart.map) hcoverH (fun i => (C i).chart.map ≫ f)
    (fun i => (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap (C i).chart.map) (fun _ => rfl) (fun _ => rfl)
    Y g K P D A (𝒮.incidenceTrace schedule) htrace hcompat ht'
  exact ⟨Z, h, L, Q, ⟨{
    indices := ι
    finite := inferInstance
    nonempty := inferInstance
    point := x
    chart := C
    domain := inferInstance
    carrierIntegral := inferInstance
    carrierDimension := hdH
    cover := hcover
    coefficientNonzero := hC
    endpoint := Y
    structureMap := g
    ideal := K
    localPrefix := P
    certificate := certificate
    comparisonMap := r
    comparison := hr
    trace := hQ
    terminal := by simpa only [Nat.add_sub_cancel] using hterm }⟩⟩

end

/-! Finite normal atlases on a finite family share one intrinsic coefficient schedule and retain all gluing certificates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_modeled_uniform_carrier_atlas_programs {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    (n : ℕ) {β τ : Type} [Fintype β] [DecidableEq β] [Fintype τ]
    (X : τ → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hJ : ∀ i, J i ≠ ⊥) (hd : ∀ i, topologicalKrullDim (X i) ≤ (d + 1 : ℕ))
    (D : ∀ i, β → (X i).IdealSheafData) (A : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ])
    (ι : τ → Type) [∀ i, Fintype (ι i)] [∀ i, Nonempty (ι i)] (x : ∀ i, ι i → X i)
    (C : ∀ i a, GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart (f i) (J i) n (D i) (x i a))
    [∀ i a, IsDomain (C i a).chart.ring] [∀ i a, IsIntegral (C i a).chart.nativeCarrier.subscheme]
    (hcover : ∀ i y, y ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i) (J i) n).support →
      ∃ a p, (C i a).chart.map p = y)
    (hC : ∀ i a, GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf ((C i a).chart.map ≫ f i)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf (f i) (J i) n).comap (C i a).chart.map) (n + 1)
        (C i a).chart.nativeCarrier.subschemeι ≠ ⊥) :
    ∃ schedule : 𝒮.Schedule (n + 1).factorial β, ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (X i) (f i) (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf (f i) (J i) n) Y g K),
        Nonempty (UniformCarrierAtlasProgram.Construction.ModeledUniformCarrierAtlasProgram 𝒮 schedule (f i) (J i) (D i) P) := by
  classical
  let κ := Σ i, ι i
  let U (s : κ) := Spec (C s.1 s.2).chart.ring
  let q (s : κ) := (C s.1 s.2).chart.map
  let H (s : κ) := (C s.1 s.2).chart.nativeCarrier
  let : ∀ s : κ, IsNoetherianRing (C s.1 s.2).chart.ring :=
    fun s => Algebra.FiniteType.isNoetherianRing ℂ (C s.1 s.2).chart.ring
  let : ∀ s : κ, IsIntegral (U s) := fun _ => inferInstance
  let : ∀ s : κ, IsLocallyNoetherian (U s) := fun _ => inferInstance
  let : ∀ s : κ, CompactSpace (U s) := fun _ => inferInstance
  let : ∀ s : κ, IsIntegral (H s).subscheme :=
    fun s => inferInstanceAs (IsIntegral (C s.1 s.2).chart.nativeCarrier.subscheme)
  let : ∀ s : κ, Smooth ((H s).subschemeι ≫ (q s ≫ f s.1)) :=
    fun s => (C s.1 s.2).chart.nativeCarrier_smooth
  have hdU (s : κ) : topologicalKrullDim (U s) ≤ (d + 1 : ℕ) :=
    (q s).isOpenEmbedding.isInducing.topologicalKrullDim_le.trans (hd s.1)
  have hdH (i : τ) (a : ι i) : topologicalKrullDim (C i a).chart.nativeCarrier.subscheme ≤ d := by
    let : IsIntegral (Spec (C i a).chart.ring) := inferInstanceAs (IsIntegral (U ⟨i, a⟩))
    let : IsLocallyNoetherian (Spec (C i a).chart.ring) := inferInstanceAs (IsLocallyNoetherian (U ⟨i, a⟩))
    exact Global.CartierDimension.Construction.locallyPrincipal_subscheme_dimension_le (C i a).chart.nativeCarrier
      ((C i a).chart.native_boundaryAtlas.component_ne_bot none)
      ((C i a).chart.native_boundaryAtlas.component_locallyPrincipal none) d (hdU ⟨i, a⟩)
  obtain ⟨schedule, hprograms⟩ := Finite.UniformCoefficientCarrierPrograms.Construction.exists_finite_uniform_coefficient_carrier_programs 𝒮 n U
    (fun s => q s ≫ f s.1) (fun s => (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf (f s.1) (J s.1) n).comap (q s))
    H hdU (fun s l => (D s.1 l).comap (q s))
    (fun s => (C s.1 s.2).chart.native_boundaryAtlas)
    (fun s => (C s.1 s.2).chart.nativeCarrier_tangent) (fun s => hC s.1 s.2)
  refine ⟨schedule, ?_⟩
  intro i
  choose Y g K P cert htrace ht using fun a : ι i => hprograms ⟨i, a⟩
  let : ∀ a, Smooth ((C i a).chart.nativeCarrier.subschemeι ≫ ((C i a).chart.map ≫ f i)) :=
    fun a => (C i a).chart.nativeCarrier_smooth
  exact exists_glued_modeled_uniform_carrier_atlas_program 𝒮 (f i) (J i) (hJ i) n (D i) (A i)
    (x i) (C i) (hdH i) (hcover i) (hC i) schedule Y g K P (fun a => (cert a).some) htrace ht

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.UniformCarrierAtlasPrograms.Construction
