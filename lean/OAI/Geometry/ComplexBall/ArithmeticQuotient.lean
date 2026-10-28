import OAI.Geometry.ComplexBall.ArithmeticPresentation
import OAI.Geometry.ComplexBall.Congruence

/-! # Arithmetic Quotient -/

namespace OAI.Geometry.ComplexBall.ArithmeticQuotient

noncomputable section

section

/-! Application of the corrected Lattices specification as an explicit input.
All geometric realizations and the integral stabilizer in its hypotheses
are supplied by the constructions in the preceding ArithmeticQuotient helper files. -/

open scoped Classical
open _root_.NumberField _root_.Topology

/-- The supplied Lattices proposition over the specified number field. -/
def ArithmeticLatticeInput (k : Type) [Field k] [NumberField k] : Prop :=
  ∀ {Gk GInf : Type} [Group Gk] [Group GInf]
    [TopologicalSpace GInf] [IsTopologicalGroup GInf] [T2Space GInf]
    [LocallyCompactSpace GInf] [SecondCountableTopology GInf]
    (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.ConnectedSemisimpleKGroup k) (δ : Gk →* GInf) (Γ₀ Γ : Subgroup Gk),
    NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.IsArithmeticPresentation G δ Γ₀ → Γ.Commensurable Γ₀ →
      NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.IsLattice (Γ.map δ) ∧
      (NumberTheory.ArithmeticGroups.Lattices.Algebraic.IsAnisotropic G → CompactSpace (GInf ⧸ Γ.map δ)) ∧
      ((∃ v : k →+* ℝ, NumberTheory.ArithmeticGroups.Lattices.Algebraic.IsCompactAtRealPlace G v) →
        NumberTheory.ArithmeticGroups.Lattices.Algebraic.IsAnisotropic G ∧ CompactSpace (GInf ⧸ Γ.map δ))

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem principalUnitary_lattice_compact (hLattices : ArithmeticLatticeInput (ArithmeticQuotientEquationsData.RealField E))
    (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (μ : E →+* ℂ)
    (hpos : ∀ ν : E →+* ℂ, ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ → 0 < (ν b).re)
    (hother : ∃ ν : E →+* ℂ, ν ≠ μ ∧ ν ≠ (starRingEnd ℂ).comp μ)
    (N : ℕ) (hN : 0 < N) :
    NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.IsLattice ((Congruence.ArithmeticQuotient.principalUnitarySubgroup b N).map (ArithmeticQuotientEquationsData.infinitePlaceMap b μ)) ∧
      CompactSpace (ArithmeticQuotientEquationsData.ArchimedeanSU b μ ⧸ (Congruence.ArithmeticQuotient.principalUnitarySubgroup b N).map (ArithmeticQuotientEquationsData.infinitePlaceMap b μ)) := by
  let G := Connected.ArithmeticQuotient.originalConnectedSemisimpleUnitaryGroup b hb hb0 δ hδ hδ0
  have hmodel := ArithmeticPresentation.Quotient.originalUnitary_arithmeticPresentation b hb hb0 δ hδ hδ0 μ hpos
  have ha := hLattices G (ArithmeticQuotientEquationsData.infinitePlaceMap b μ) (Congruence.ArithmeticQuotient.integralUnitarySubgroup b)
    (Congruence.ArithmeticQuotient.principalUnitarySubgroup b N) hmodel (Congruence.ArithmeticQuotient.principalUnitary_commensurable b N hN)
  obtain ⟨ν, hν, hνc⟩ := hother
  have hc : NumberTheory.ArithmeticGroups.Lattices.Algebraic.IsCompactAtRealPlace G (RealPlaces.ArithmeticQuotient.realEmbedding ν) :=
    RealPlaces.ArithmeticQuotient.originalUnitaryPoints_compact b hb δ hδ hδ0 (RealPlaces.ArithmeticQuotient.realEmbedding ν) (hpos ν hν hνc)
  exact ⟨ha.1, (ha.2.2 ⟨RealPlaces.ArithmeticQuotient.realEmbedding ν, hc⟩).2⟩

end

/-! Transport to the complex image of E, so the universe-zero Lattices interface
applies without restricting the universe of the original number field. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.Algebra OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

lemma cmField_of_ringEquiv {E L : Type*} [Field E] [NumberField E] [IsCMField E]
    [Field L] [NumberField L] (e : E ≃+* L) : IsCMField L := by
  let : IsTotallyComplex L := ⟨fun w =>
    InfinitePlace.IsComplex.of_comap e.toRingHom (IsTotallyComplex.isComplex _)⟩
  let : Algebra (ArithmeticQuotientEquationsData.RealField E) L := (e.toRingHom.comp (algebraMap (ArithmeticQuotientEquationsData.RealField E) E)).toAlgebra
  let : IsQuadraticExtension (ArithmeticQuotientEquationsData.RealField E) L := ⟨by
    calc
      Module.finrank (ArithmeticQuotientEquationsData.RealField E) L = Module.finrank (ArithmeticQuotientEquationsData.RealField E) E :=
        Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl (ArithmeticQuotientEquationsData.RealField E)) e.symm (by
          ext x
          change (x : E) = e.symm (e (x : E))
          exact (e.symm_apply_apply _).symm)
      _ = 2 := IsQuadraticExtension.finrank_eq_two (ArithmeticQuotientEquationsData.RealField E) E⟩
  exact IsCMField.ofCMExtension (ArithmeticQuotientEquationsData.RealField E) L

lemma ringEquiv_complexConj {E L : Type*} [Field E] [NumberField E] [IsCMField E]
    [Field L] [NumberField L] [IsCMField L] (e : E ≃+* L) (x : E) :
    e (IsCMField.complexConj E x) = IsCMField.complexConj L (e x) := by
  let ν : L →+* ℂ := Classical.choice inferInstance
  apply ν.injective
  exact (IsCMField.complexEmbedding_complexConj E (ν.comp e.toRingHom) x).trans
    (IsCMField.complexEmbedding_complexConj L ν (e x)).symm

section Principal
variable {E L : Type*} [Field E] [NumberField E] [IsCMField E]
    [Field L] [NumberField L] [IsCMField L]

def cmUnitaryEquiv (b : E) (e : E ≃+* L) : ArithmeticQuotientEquationsData.RationalSU b ≃* ArithmeticQuotientEquationsData.RationalSU (e b) :=
  ArithmeticQuotientSplitUnitary.unitaryEquiv _ _ b e (ringEquiv_complexConj e)

lemma cmUnitaryEquiv_mem_principal (b : E) (N : ℕ) (e : E ≃+* L) (g : ArithmeticQuotientEquationsData.RationalSU b) :
    cmUnitaryEquiv b e g ∈ Congruence.ArithmeticQuotient.principalUnitarySubgroup (e b) N ↔
      g ∈ Congruence.ArithmeticQuotient.principalUnitarySubgroup b N := by
  rw [Congruence.ArithmeticQuotient.mem_principalUnitarySubgroup, Congruence.ArithmeticQuotient.mem_principalUnitarySubgroup]
  constructor
  · rintro ⟨_, _, B, hB⟩
    refine ⟨g.val.property, g.property,
      fun i j => ⟨e.symm (B i j), map_isIntegral_int e.symm (B i j).property⟩, ?_⟩
    intro i j
    have he := congrArg e.symm (hB i j)
    change e.symm (e (g.val i j) - (1 : ArithmeticQuotientEquationsData.Mat L) i j) = _ at he
    change g.val i j - (1 : ArithmeticQuotientEquationsData.Mat E) i j = (N : E) * e.symm (B i j)
    simpa only [map_sub, map_mul, map_natCast, RingEquiv.symm_apply_apply,
      Matrix.one_apply, apply_ite, map_one, map_zero] using he
  · rintro ⟨_, _, B, hB⟩
    refine ⟨(cmUnitaryEquiv b e g).val.property, (cmUnitaryEquiv b e g).property,
      fun i j => ⟨e (B i j), map_isIntegral_int e (B i j).property⟩, ?_⟩
    intro i j
    have he := congrArg e (hB i j)
    change e (g.val i j) - (1 : ArithmeticQuotientEquationsData.Mat L) i j = (N : L) * e (B i j)
    simpa only [map_sub, map_mul, map_natCast,
      Matrix.one_apply, apply_ite, map_one, map_zero] using he

lemma principalImage_ringEquiv (b : E) (N : ℕ) (e : E ≃+* L) (ν : L →+* ℂ) :
    (Congruence.ArithmeticQuotient.principalUnitarySubgroup b N).map (ArithmeticQuotientEquationsData.infinitePlaceMap b (ν.comp e.toRingHom)) =
      (Congruence.ArithmeticQuotient.principalUnitarySubgroup (e b) N).map (ArithmeticQuotientEquationsData.infinitePlaceMap (e b) ν) := by
  have he (g : ArithmeticQuotientEquationsData.RationalSU b) :
      ArithmeticQuotientEquationsData.infinitePlaceMap b (ν.comp e.toRingHom) g =
        ArithmeticQuotientEquationsData.infinitePlaceMap (e b) ν (cmUnitaryEquiv b e g) := rfl
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨cmUnitaryEquiv b e x, (cmUnitaryEquiv_mem_principal b N e x).mpr hx, (he x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := (cmUnitaryEquiv b e).surjective x
    exact ⟨y, (cmUnitaryEquiv_mem_principal b N e y).mp hx, he y⟩

end Principal

/-- Lattices is used only on the universe-zero image field in C. All principal
matrices, including their exact integer level, are transported by equality
of their complex images. -/
theorem principalUnitary_lattice_compact_universe
    (hLattices : ∀ (k : Type) [Field k] [NumberField k], ArithmeticLatticeInput k)
    {E : Type*} [Field E] [NumberField E] [IsCMField E]
    (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
    (μ : E →+* ℂ)
    (hpos : ∀ ν : E →+* ℂ, ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ → 0 < (ν b).re)
    (hother : ∃ ν : E →+* ℂ, ν ≠ μ ∧ ν ≠ (starRingEnd ℂ).comp μ)
    (N : ℕ) (hN : 0 < N) :
    NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.IsLattice ((Congruence.ArithmeticQuotient.principalUnitarySubgroup b N).map (ArithmeticQuotientEquationsData.infinitePlaceMap b μ)) ∧
      CompactSpace (ArithmeticQuotientEquationsData.ArchimedeanSU b μ ⧸ (Congruence.ArithmeticQuotient.principalUnitarySubgroup b N).map (ArithmeticQuotientEquationsData.infinitePlaceMap b μ)) := by
  let L : Type := μ.fieldRange
  let e : E ≃+* L := μ.rangeRestrictFieldEquiv
  let : NumberField L := NumberField.of_ringEquiv E L e
  let : IsCMField L := cmField_of_ringEquiv e
  let ν : L →+* ℂ := μ.fieldRange.subtype
  have hc : IsCMField.complexConj L (e b) = e b :=
    (ringEquiv_complexConj e b).symm.trans (congrArg e hb)
  have hnonzero : e b ≠ 0 := (map_ne_zero e).mpr hb0
  have hp : ∀ ψ : L →+* ℂ, ψ ≠ ν → ψ ≠ (starRingEnd ℂ).comp ν → 0 < (ψ (e b)).re := by
    intro ψ hψ hψc
    apply hpos (ψ.comp e.toRingHom)
    · intro h
      apply hψ
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      exact RingHom.congr_fun h x
    · intro h
      apply hψc
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      exact RingHom.congr_fun h x
  have ho : ∃ ψ : L →+* ℂ, ψ ≠ ν ∧ ψ ≠ (starRingEnd ℂ).comp ν := by
    obtain ⟨ψ, hψ, hψc⟩ := hother
    refine ⟨ψ.comp e.symm.toRingHom, ?_, ?_⟩
    · intro h
      apply hψ
      ext x
      have hx := RingHom.congr_fun h (e x)
      change ψ (e.symm (e x)) = μ x at hx
      simpa only [RingEquiv.symm_apply_apply] using hx
    · intro h
      apply hψc
      ext x
      have hx := RingHom.congr_fun h (e x)
      change ψ (e.symm (e x)) = (starRingEnd ℂ) (μ x) at hx
      change ψ x = (starRingEnd ℂ) (μ x)
      simpa only [RingEquiv.symm_apply_apply] using hx
  obtain ⟨δ, hδ0, hδ⟩ := ArithmeticQuotientEquationsData.exists_imaginary_generator (E := L)
  have ha := principalUnitary_lattice_compact (hLattices (ArithmeticQuotientEquationsData.RealField L)) (e b) hc hnonzero
    δ hδ hδ0 ν hp ho N hN
  have hgroup : (Congruence.ArithmeticQuotient.principalUnitarySubgroup b N).map (ArithmeticQuotientEquationsData.infinitePlaceMap b μ) =
      (Congruence.ArithmeticQuotient.principalUnitarySubgroup (e b) N).map (ArithmeticQuotientEquationsData.infinitePlaceMap (e b) ν) :=
    principalImage_ringEquiv b N e ν
  exact hgroup.symm ▸ ha

end

end OAI.Geometry.ComplexBall.ArithmeticQuotient
