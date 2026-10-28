import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCompact
import OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator
import OAI.RepresentationTheory.Weil.AdelicSplitting.Integral

/-! # Vacuum -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction

noncomputable section

/-! Integral symplectic groups and the actual unramified vacuum.
The cover's restricted subgroup fixes the characteristic function of O_v^N. -/

open scoped _root_.NumberField Classical
open IsDedekindDomain Filter

def mapSymplectic {R S : Type*} [CommRing R] [CommRing S] (N : ℕ) (f : R →+* S) :
    Matrix.symplecticGroup (Fin N) R →* Matrix.symplecticGroup (Fin N) S where
  toFun g := ⟨g.val.map f, SymplecticGroup.map_mem g.property f⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by apply Subtype.ext; exact Matrix.map_mul

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def symplecticIntegral (v : ArchimedeanAdeles.Construction.Places F) : Subgroup (Local.FunctionsMetaplectic.Construction.Symplectic (ArchimedeanAdeles.Construction.Completion F v) N) :=
  Integral.Construction.integralMatrixGroup (Matrix.symplecticGroup (Fin N) (ArchimedeanAdeles.Construction.Completion F v)).subtype
    (Integral.Construction.localIntegerRing F v)

def rationalSymplecticLocal (v : ArchimedeanAdeles.Construction.Places F) : Local.FunctionsMetaplectic.Construction.Symplectic F N →* Local.FunctionsMetaplectic.Construction.Symplectic (ArchimedeanAdeles.Construction.Completion F v) N :=
  mapSymplectic N (ArchimedeanAdeles.Construction.rationalScalar F v)

theorem rationalSymplecticLocal_integral (g : Local.FunctionsMetaplectic.Construction.Symplectic F N) :
    ∀ᶠ v in cofinite, rationalSymplecticLocal F N v g ∈ symplecticIntegral F N v := by
  have hv : ∀ᶠ v in cofinite, ∀ i j, ArchimedeanAdeles.Construction.rationalScalar F v (g.val i j) ∈ Integral.Construction.localIntegerRing F v :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      Integral.Construction.rationalScalar_integral F (g.val i j)
  have hi : ∀ᶠ v in cofinite, ∀ i j, ArchimedeanAdeles.Construction.rationalScalar F v ((g⁻¹).val i j) ∈ Integral.Construction.localIntegerRing F v :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      Integral.Construction.rationalScalar_integral F ((g⁻¹).val i j)
  filter_upwards [hv, hi] with v hv hi
  refine ⟨hv, ?_⟩
  intro i j
  change ((rationalSymplecticLocal F N v g)⁻¹).val i j ∈ Integral.Construction.localIntegerRing F v
  rw [← map_inv]
  exact hi i j

abbrev AdelicSymplectic := RestrictedLimits.Construction.RestrictedGroup (symplecticIntegral F N)

def rationalSymplectic : Local.FunctionsMetaplectic.Construction.Symplectic F N →* AdelicSymplectic F N :=
  RestrictedLimits.Construction.diagonalMap (symplecticIntegral F N) (rationalSymplecticLocal F N)
    (rationalSymplecticLocal_integral F N)

def finitePositionLattice (v : HeightOneSpectrum (𝓞 F)) : Set (Local.FunctionsMetaplectic.Construction.Position (v.adicCompletion F) N) :=
  Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))

theorem finitePositionLattice_clopen (v : HeightOneSpectrum (𝓞 F)) :
    IsClopen (finitePositionLattice F N v) := by
  constructor
  · exact isClosed_set_pi fun _ _ => Valued.isClosed_integer _
  · exact isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_integer _

theorem finitePositionLattice_compact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (finitePositionLattice F N v) := by
  have h : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
      Metric.closedBall (0 : v.adicCompletion F) 1 := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right,
      Valued.toNormedField.norm_le_one_iff]
    rfl
  have hc : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rw [h]
    exact isCompact_closedBall 0 1
  simpa [finitePositionLattice, Set.pi] using
    (isCompact_pi_infinite fun _ : Fin N => hc)

def finiteVacuum (v : HeightOneSpectrum (𝓞 F)) : Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N := by
  let f := LocallyConstant.charFn ℂ (finitePositionLattice_clopen F N v)
  refine ⟨f, Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem f.isLocallyConstant ?_⟩
  apply HasCompactSupport.intro (finitePositionLattice_compact F N v)
  intro x hx
  exact Set.indicator_of_notMem hx 1

theorem finiteVacuum_zero (v : HeightOneSpectrum (𝓞 F)) :
    (finiteVacuum F N v).val 0 = 1 := by
  change (LocallyConstant.charFn ℂ (finitePositionLattice_clopen F N v)) 0 = 1
  apply (LocallyConstant.charFn_eq_one ℂ 0 (finitePositionLattice_clopen F N v)).mpr
  intro i hi
  exact (v.adicCompletionIntegers F).zero_mem

variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

abbrev CoverAt (v : ArchimedeanAdeles.Construction.Places F) :=
  Oscillator.Construction.LocalCover (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)

def projectionAt (v : ArchimedeanAdeles.Construction.Places F) : CoverAt F N ψ v →* Local.FunctionsMetaplectic.Construction.Symplectic (ArchimedeanAdeles.Construction.Completion F v) N :=
  Oscillator.Construction.localProjection (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)

def scalarAt (v : ArchimedeanAdeles.Construction.Places F) : Circle →* CoverAt F N ψ v :=
  Oscillator.Construction.localScalar (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)

def coverIntegral (v : ArchimedeanAdeles.Construction.Places F) : Subgroup (CoverAt F N ψ v) :=
  (symplecticIntegral F N v).comap (projectionAt F N ψ v) ⊓
    match v with
    | Sum.inl _ => ⊤
    | Sum.inr p =>
      letI : MeasurableSpace (p.adicCompletion F) := ArchimedeanAdeles.Construction.completionMeasurableSpace F (Sum.inr p)
      letI : BorelSpace (p.adicCompletion F) := ArchimedeanAdeles.Construction.completionBorelSpace F (Sum.inr p)
      Oscillator.Construction.vacuumStabilizer (p.adicCompletion F) N
        (Characters.Construction.localAdditiveCharacter F ψ (Sum.inr p)) (finiteVacuum F N p)

theorem coverIntegral_projects (v : ArchimedeanAdeles.Construction.Places F) :
    Set.MapsTo (projectionAt F N ψ v) (coverIntegral F N ψ v) (symplecticIntegral F N v) :=
  fun _ h => h.1

abbrev GlobalCover := CentralProduct.Construction.AdelicCover (coverIntegral F N ψ) (scalarAt F N ψ)

def globalProjection : GlobalCover F N ψ →* AdelicSymplectic F N :=
  CentralProduct.Construction.adelicProjection (coverIntegral F N ψ) (symplecticIntegral F N) (scalarAt F N ψ)
    (projectionAt F N ψ) (Filter.Eventually.of_forall (coverIntegral_projects F N ψ))
    (fun v z => Oscillator.Construction.localProjection_scalar (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) z)

def globalInclude (v : ArchimedeanAdeles.Construction.Places F) : CoverAt F N ψ v →ₜ* GlobalCover F N ψ :=
  CentralProduct.Construction.includeCoverContinuous (coverIntegral F N ψ) (scalarAt F N ψ) v

@[simp] theorem globalProjection_include (v : ArchimedeanAdeles.Construction.Places F) (g : CoverAt F N ψ v) :
    globalProjection F N ψ (globalInclude F N ψ v g) =
      RestrictedLimits.Construction.includePlace (symplecticIntegral F N) v (projectionAt F N ψ v g) :=
  CentralProduct.Construction.adelicProjection_include (coverIntegral F N ψ) (symplecticIntegral F N) (scalarAt F N ψ)
    (projectionAt F N ψ) (Filter.Eventually.of_forall (coverIntegral_projects F N ψ))
    (fun w z => Oscillator.Construction.localProjection_scalar (ArchimedeanAdeles.Construction.Completion F w) N (Characters.Construction.localAdditiveCharacter F ψ w) z) v g

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction
