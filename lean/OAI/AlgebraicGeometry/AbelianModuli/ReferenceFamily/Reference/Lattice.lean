import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Action
import OAI.NumberTheory.ArithmeticGroups.Trace

/-! # Lattice -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

section

/-! Identify the actual analytic period lattice with the original
marked lattice, with the exact integral polarization and CM adjoints. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z)

def Fiber.ReferenceAnalyticFiber.periodEmbedding : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →+ Fiber.ReferenceTangent s where
  toFun v := F.projection (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings v)
  map_zero' := by
    have hz : Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings (0 : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) = 0 := by
      ext i <;> simp [Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates]
    rw [hz, map_zero]
  map_add' v w := by
    have ha : Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings (v + w) =
        Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings v + Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings w := by
      ext i <;> simp [Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates]
    rw [ha, map_add]

def Fiber.ReferenceAnalyticFiber.latticeMap : P.lattice →+ F.lattice where
  toFun v := ⟨F.periodEmbedding v.val, (F.lattice_membership _).mpr ⟨v.val, v.property, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero F.periodEmbedding)
  map_add' v w := Subtype.ext (map_add F.periodEmbedding v.val w.val)

theorem Fiber.ReferenceAnalyticFiber.latticeMap_bijective : Function.Bijective F.latticeMap := by
  constructor
  · intro v w h
    exact Subtype.ext (F.embedding_injective (congrArg Subtype.val h))
  · intro v
    obtain ⟨w, hw, he⟩ := (F.lattice_membership v.val).mp v.property
    exact ⟨⟨w, hw⟩, Subtype.ext he.symm⟩

def Fiber.ReferenceAnalyticFiber.latticeEquiv : P.lattice ≃+ F.lattice := AddEquiv.ofBijective F.latticeMap F.latticeMap_bijective

@[simp] theorem Fiber.ReferenceAnalyticFiber.latticeEquiv_apply (v : P.lattice) :
    (F.latticeEquiv v).val = F.periodEmbedding v.val := rfl

theorem Fiber.ReferenceAnalyticFiber.latticeEquiv_polarization (hP : P.IsAdmissible) (v w : P.lattice) :
    (F.form (F.latticeEquiv v).val (F.latticeEquiv w).val).im = (P.integralForm v w : ℝ) := by
  rw [Fiber.ReferenceAnalyticFiber.latticeEquiv_apply, Fiber.ReferenceAnalyticFiber.latticeEquiv_apply]
  change (F.form (F.projection _) (F.projection _)).im = _
  rw [F.polarization]
  rcases hP with ⟨_, _, _, _, _, _, _, _, _, _, hi, _⟩
  rw [← hi v w]
  exact Rat.cast_intCast _

theorem Fiber.ReferenceAnalyticFiber.form_integral (hP : P.IsAdmissible) (u v : F.lattice) :
    ∃ n : ℤ, (F.form u.val v.val).im = (n : ℝ) := by
  obtain ⟨a, rfl⟩ := F.latticeEquiv.surjective u
  obtain ⟨b, rfl⟩ := F.latticeEquiv.surjective v
  exact ⟨P.integralForm a b, F.latticeEquiv_polarization hP a b⟩

theorem Fiber.ReferenceAnalyticFiber.form_rosati_on_reference (a : NumberField.RingOfIntegers E) (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (F.form (F.action a (F.periodEmbedding v)) (F.periodEmbedding w)).im =
      (F.form (F.periodEmbedding v)
        (F.action (NumberField.IsCMField.ringOfIntegersComplexConj E a) (F.periodEmbedding w))).im := by
  change (F.form (F.action a (F.projection _)) (F.projection _)).im =
    (F.form (F.projection _) (F.action _ (F.projection _))).im
  rw [F.equivariant, F.equivariant, F.polarization, F.polarization]
  apply congrArg (fun t : ℚ => (t : ℝ))
  unfold Datum.RankThreePELDatum.traceForm
  congr 1
  exact NumberTheory.ArithmeticGroups.Trace.CongruenceLevel.trace_rosati _ _ _ _ _

end

/-! The imaginary part of the reference Hermitian form is a
nondegenerate real alternating pairing with the exact CM adjoints. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z)

def Fiber.ReferenceAnalyticFiber.imaginaryForm : Fiber.ReferenceTangent s →ₗ[ℝ] Fiber.ReferenceTangent s →ₗ[ℝ] ℝ where
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

theorem Fiber.ReferenceAnalyticFiber.imaginaryForm_skew (u v : Fiber.ReferenceTangent s) :
    F.imaginaryForm v u = -F.imaginaryForm u v := by
  change (F.form v u).im = -(F.form u v).im
  rw [F.hermitian]
  rfl

theorem Fiber.ReferenceAnalyticFiber.imaginaryForm_nondegenerate : F.imaginaryForm.Nondegenerate := by
  have hleft : F.imaginaryForm.SeparatingLeft := by
    intro u hu
    by_contra hne
    have hz := hu (Complex.I • u)
    have hpos := F.positive u hne
    change (F.form u (Complex.I • u)).im = 0 at hz
    rw [map_smul] at hz
    simp only [smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_add] at hz
    exact (ne_of_gt hpos) hz
  refine ⟨hleft, ?_⟩
  intro u hu
  apply hleft u
  intro v
  rw [F.imaginaryForm_skew v u, hu v, neg_zero]

theorem Fiber.ReferenceAnalyticFiber.form_rosati_im (a : NumberField.RingOfIntegers E) (u v : Fiber.ReferenceTangent s) :
    (F.form (F.action a u) v).im =
      (F.form u (F.action (NumberField.IsCMField.ringOfIntegersComplexConj E a) v)).im := by
  let B := F.imaginaryForm.comp ((F.action a).restrictScalars ℝ)
  let C := F.imaginaryForm.compl₂
    ((F.action (NumberField.IsCMField.ringOfIntegersComplexConj E a)).restrictScalars ℝ)
  have hspan : Submodule.span ℝ (F.lattice : Set (Fiber.ReferenceTangent s)) = ⊤ := by
    let : CompactSpace (Fiber.ReferenceTangent s ⧸ F.lattice.toIntSubmodule.toAddSubgroup) := F.compact
    exact RepresentationTheory.Theta.Geometric.CompactLattice.span_top_of_compact_quotient F.lattice.toIntSubmodule
  have hBC : B = C := by
    apply LinearMap.ext_on hspan
    intro a' ha'
    apply LinearMap.ext_on hspan
    intro b' hb'
    obtain ⟨a₀, _, rfl⟩ := (F.lattice_membership a').mp ha'
    obtain ⟨b₀, _, rfl⟩ := (F.lattice_membership b').mp hb'
    exact F.form_rosati_on_reference a a₀ b₀
  exact DFunLike.congr_fun (DFunLike.congr_fun hBC u) v

theorem Fiber.ReferenceAnalyticFiber.form_rosati (a : NumberField.RingOfIntegers E) (u v : Fiber.ReferenceTangent s) :
    F.form (F.action a u) v =
      F.form u (F.action (NumberField.IsCMField.ringOfIntegersComplexConj E a) v) := by
  apply Complex.ext
  · have h := F.form_rosati_im a u (Complex.I • v)
    rw [map_smul, map_smul, map_smul] at h
    simpa only [smul_eq_mul, Complex.I_mul_im] using h
  · exact F.form_rosati_im a u v

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
