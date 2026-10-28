import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.Tangent
import OAI.RepresentationTheory.Theta.Geometric.Torus.Manifold
import OAI.NumberTheory.ArithmeticGroups.Trace

/-! # Action -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! The prescribed integral CM action acts holomorphically on the actual
reference period quotient. Lattice stability is derived from the original
reference lattice and the analytic fiber's equivariance equation. -/

open scoped _root_.Manifold ContDiff

section

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

variable {x : D.domain} (F : D.ReferenceAnalyticFiber x)

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.action_preserves_lattice (hg : D.pel.HasIntegralModelGeometry)
    (a : NumberField.RingOfIntegers E) (v : Data.ActiveHeckeThetaData.referenceTangent (s := s)) (hv : v ∈ F.lattice) :
    F.action a v ∈ F.lattice := by
  obtain ⟨w, hw, rfl⟩ := (F.lattice_membership v).mp hv
  rw [F.equivariant]
  apply (F.lattice_membership _).mpr
  rcases hg.reference_admissible with ⟨_, _, _, _, _, _, _, _, _, hL, _⟩
  exact ⟨(a : E) • w, hL.2.2 a w hw, rfl⟩

def Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.quotientAction (hg : D.pel.HasIntegralModelGeometry) (a : NumberField.RingOfIntegers E) :
    (F.periodData D).periodTorus →+ (F.periodData D).periodTorus :=
  QuotientAddGroup.map F.lattice F.lattice (F.action a).toAddMonoidHom
    (fun v hv => F.action_preserves_lattice D hg a v hv)

@[simp] theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.quotientAction_mk (hg : D.pel.HasIntegralModelGeometry)
    (a : NumberField.RingOfIntegers E) (v : Data.ActiveHeckeThetaData.referenceTangent (s := s)) :
    F.quotientAction D hg a (QuotientAddGroup.mk v) = QuotientAddGroup.mk (F.action a v) := rfl

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.quotientAction_contMDiff (hg : D.pel.HasIntegralModelGeometry)
    (a : NumberField.RingOfIntegers E) :
    ContMDiff 𝓘(ℂ, (F.periodData D).space) 𝓘(ℂ, (F.periodData D).space) ∞
      (F.quotientAction D hg a) := by
  apply (F.periodData D).contMDiff_of_periodProjection
  exact (F.periodData D).periodProjection_contMDiff.comp
    (LinearMap.toContinuousLinearMap (F.action a)).contDiff.contMDiff

end

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  {x : D.domain} (F : D.ReferenceAnalyticFiber x)

def Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.quotientRingAction (hg : D.pel.HasIntegralModelGeometry) :
    NumberField.RingOfIntegers E →+* AddMonoid.End (F.periodData D).periodTorus where
  toFun := F.quotientAction D hg
  map_zero' := by
    ext z
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    change QuotientAddGroup.mk (F.action 0 v) = (0 : (F.periodData D).periodTorus)
    rw [map_zero]
    rfl
  map_one' := by
    ext z
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    change QuotientAddGroup.mk (F.action 1 v) = QuotientAddGroup.mk v
    rw [map_one]
    rfl
  map_add' := by
    intro a b
    ext z
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    change QuotientAddGroup.mk (F.action (a + b) v) =
      QuotientAddGroup.mk (F.action a v) + QuotientAddGroup.mk (F.action b v)
    rw [map_add]
    exact QuotientAddGroup.mk_add F.lattice (F.action a v) (F.action b v)
  map_mul' := by
    intro a b
    ext z
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    change QuotientAddGroup.mk (F.action (a * b) v) =
      QuotientAddGroup.mk (F.action a (F.action b v))
    rw [map_mul]
    rfl

end

section

/-! The actual period lattice is identified with the marked reference
lattice, preserving its integral alternating form and CM adjoint equation. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

variable {x : D.domain} (F : D.ReferenceAnalyticFiber x)

def Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.periodEmbedding : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →+ Data.ActiveHeckeThetaData.referenceTangent (s := s) where
  toFun v := F.projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v)
  map_zero' := by
    have hz : Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings (0 : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) = 0 := by
      ext i <;> simp [Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates]
    rw [hz, map_zero]
  map_add' v w := by
    have ha : Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings (v + w) =
        Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v +
          Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings w := by
      ext i <;> simp [Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates]
    rw [ha, map_add]

def Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.latticeMap : D.pel.reference.lattice →+ F.lattice where
  toFun v := ⟨F.periodEmbedding D v.val,
    (F.lattice_membership _).mpr ⟨v.val, v.property, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero (F.periodEmbedding D))
  map_add' v w := Subtype.ext (map_add (F.periodEmbedding D) v.val w.val)

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.latticeMap_bijective : Function.Bijective (F.latticeMap D) := by
  constructor
  · intro v w h
    exact Subtype.ext (F.embedding_injective (congrArg Subtype.val h))
  · intro v
    obtain ⟨w, hw, he⟩ := (F.lattice_membership v.val).mp v.property
    exact ⟨⟨w, hw⟩, Subtype.ext he.symm⟩

def Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.latticeEquiv : D.pel.reference.lattice ≃+ F.lattice :=
  AddEquiv.ofBijective (F.latticeMap D) (F.latticeMap_bijective D)

@[simp] theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.latticeEquiv_apply (v : D.pel.reference.lattice) :
    (F.latticeEquiv D v).val = F.periodEmbedding D v.val := rfl

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.latticeEquiv_polarization (hg : D.pel.HasIntegralModelGeometry)
    (v w : D.pel.reference.lattice) :
    (F.form (F.latticeEquiv D v).val (F.latticeEquiv D w).val).im =
      (D.pel.reference.integralForm v w : ℝ) := by
  rw [Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.latticeEquiv_apply, Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.latticeEquiv_apply]
  change (F.form (F.projection _) (F.projection _)).im = _
  rw [F.polarization]
  rcases hg.reference_admissible with ⟨_, _, _, _, _, _, _, _, _, _, hi, _⟩
  rw [← hi v w]
  exact Rat.cast_intCast _

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.form_integral (hg : D.pel.HasIntegralModelGeometry) (u v : F.lattice) :
    ∃ n : ℤ, (F.form u.val v.val).im = (n : ℝ) := by
  obtain ⟨a, rfl⟩ := (F.latticeEquiv D).surjective u
  obtain ⟨b, rfl⟩ := (F.latticeEquiv D).surjective v
  exact ⟨D.pel.reference.integralForm a b, F.latticeEquiv_polarization D hg a b⟩

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.form_rosati_on_reference (a : NumberField.RingOfIntegers E) (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (F.form (F.action a (F.periodEmbedding D v)) (F.periodEmbedding D w)).im =
      (F.form (F.periodEmbedding D v)
        (F.action (NumberField.IsCMField.ringOfIntegersComplexConj E a)
          (F.periodEmbedding D w))).im := by
  change (F.form (F.action a (F.projection _)) (F.projection _)).im =
    (F.form (F.projection _) (F.action _ (F.projection _))).im
  rw [F.equivariant, F.equivariant, F.polarization, F.polarization]
  apply congrArg (fun t : ℚ => (t : ℝ))
  unfold AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.traceForm
  congr 1
  exact NumberTheory.ArithmeticGroups.Trace.CongruenceLevel.trace_rosati _ _ _ _ _

end

/-! The reference trace adjoint identity extends to the entire tangent
space by real bilinearity and the actual full period lattice. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

variable {x : D.domain} (F : D.ReferenceAnalyticFiber x)

def Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.imaginaryForm : Data.ActiveHeckeThetaData.referenceTangent (s := s) →ₗ[ℝ] Data.ActiveHeckeThetaData.referenceTangent (s := s) →ₗ[ℝ] ℝ where
  toFun u := Complex.imCLM.toLinearMap.comp ((F.form u).restrictScalars ℝ)
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change (F.form (u + v) w).im = (F.form u w).im + (F.form v w).im
    rw [map_add, LinearMap.add_apply, Complex.add_im]
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    change (F.form (c • u) v).im = c * (F.form u v).im
    have hc : c • u = (c : ℂ) • u := (IsScalarTower.algebraMap_smul ℂ c u).symm
    rw [hc, map_smulₛₗ, LinearMap.smul_apply]
    simp

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.form_rosati_im (a : NumberField.RingOfIntegers E)
    (u v : Data.ActiveHeckeThetaData.referenceTangent (s := s)) :
    (F.form (F.action a u) v).im =
      (F.form u (F.action (NumberField.IsCMField.ringOfIntegersComplexConj E a) v)).im := by
  let B := (F.imaginaryForm D).comp ((F.action a).restrictScalars ℝ)
  let C := (F.imaginaryForm D).compl₂
    ((F.action (NumberField.IsCMField.ringOfIntegersComplexConj E a)).restrictScalars ℝ)
  have hspan : Submodule.span ℝ (F.lattice : Set (Data.ActiveHeckeThetaData.referenceTangent (s := s))) = ⊤ := by
    let : CompactSpace ((Data.ActiveHeckeThetaData.referenceTangent (s := s)) ⧸ F.lattice.toIntSubmodule.toAddSubgroup) := F.compact
    exact CompactLattice.span_top_of_compact_quotient F.lattice.toIntSubmodule
  have hBC : B = C := by
    apply LinearMap.ext_on hspan
    intro z hz
    apply LinearMap.ext_on hspan
    intro w hw
    obtain ⟨z₀, _, rfl⟩ := (F.lattice_membership z).mp hz
    obtain ⟨w₀, _, rfl⟩ := (F.lattice_membership w).mp hw
    exact F.form_rosati_on_reference D a z₀ w₀
  exact DFunLike.congr_fun (DFunLike.congr_fun hBC u) v

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.form_rosati (a : NumberField.RingOfIntegers E)
    (u v : Data.ActiveHeckeThetaData.referenceTangent (s := s)) :
    F.form (F.action a u) v =
      F.form u (F.action (NumberField.IsCMField.ringOfIntegersComplexConj E a) v) := by
  apply Complex.ext
  · have h := F.form_rosati_im D a u (Complex.I • v)
    rw [map_smul, map_smul, map_smul] at h
    simpa only [smul_eq_mul, Complex.I_mul_im] using h
  · exact F.form_rosati_im D a u v

end

end OAI.RepresentationTheory.Theta.Geometric
