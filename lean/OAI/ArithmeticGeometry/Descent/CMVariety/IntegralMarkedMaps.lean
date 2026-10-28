import OAI.ArithmeticGeometry.Descent.CMVariety.Faithfulness
import OAI.ArithmeticGeometry.Descent.CMVariety.MarkedActions

/-! # Integral Marked Maps -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.IntegralMarkedMaps.Abelian.IntrinsicPeriods

noncomputable section

section

/-!
Naturality of the actual rational marking and preservation of designated
endomorphisms by marked group isomorphisms. Equal marked matrices yield
commuting algebraic scheme maps via the proved faithfulness of H¹.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod.Constructions.LatticeDual

variable {Index : Type} [Fintype Index]

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper A.toOver.hom :=
  A.variety.presentation.projective.isProper

/-- The pointwise marking condition forces the native linear lift to
carry every complex period vector to its counterpart. -/
theorem linear_lift_periodMap_of_marked_map {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B)
    (f : A.toOver ⟶ B.toOver) [IsMonHom f]
    (hmark : ∀ z : Index → ℂ,
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f
        (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap a z))) =
          AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z)))
    (L : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (hlift : Geometry.ComplexTorus.BettiLattice.CM.Construction.Lifts (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraicTorusMap f) L) (z : Index → ℂ) :
    L (MarkedAbelianPeriods.IntrinsicPeriods.periodMap a z) = MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z := by
  have hL (v : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj v)) =
        AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (L v)) := by
    rw [← IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.nativeMap_algebraicTorusMap f, AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.nativeMap_periodHomeomorph]
    exact congrArg (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B) (hlift v)
  apply sub_eq_zero.mp
  apply MarkedPeriodClassification.Abelian.IntrinsicPeriods.zero_of_all_smul_mem_lattice B
  intro c
  have h := (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B).injective
    ((hL (MarkedAbelianPeriods.IntrinsicPeriods.periodMap a (c • z))).symm.trans (hmark (c • z)))
  have he : (QuotientAddGroup.mk (c • L (MarkedAbelianPeriods.IntrinsicPeriods.periodMap a z)) :
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B ⧸ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B).toAddSubgroup) =
        QuotientAddGroup.mk (c • MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z) := by
    change (QuotientAddGroup.mk (L (MarkedAbelianPeriods.IntrinsicPeriods.periodMap a (c • z))) :
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B ⧸ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B).toAddSubgroup) =
        QuotientAddGroup.mk (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (c • z)) at h
    simpa only [map_smul] using h
  apply (QuotientAddGroup.eq_zero_iff _).mp
  rw [smul_sub, QuotientAddGroup.mk_sub]
  exact sub_eq_zero.mpr he

/-- A morphism respecting the native marked periods acts as the identity
between the two rational coordinate spaces. -/
theorem rationalCoordinates_pullback_of_marked_map {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B)
    (f : A.toOver ⟶ B.toOver) [IsMonHom f]
    (hmark : ∀ z : Index → ℂ,
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f
        (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap a z))) =
          AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z)))
    (c : B.variety.rationalCohomology 1) :
    MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f c) = MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b c := by
  obtain ⟨L, ⟨hL, hlift⟩, _⟩ := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraic_map_linear_lift f
  have hp := linear_lift_periodMap_of_marked_map a b f hmark L hlift
  have hb (i : Index) : L (a i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) = (b i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) := by
    have h := hp ((Pi.basisFun ℂ Index) i)
    simpa only [MarkedAbelianPeriods.IntrinsicPeriods.periodMap, Module.Basis.constr_basis] using h
  ext i
  rw [MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates_apply, MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates_apply,
    Faithfulness.Abelian.IntrinsicPeriods.rationalH1Equiv_algebraic_pullback f L hL hlift]
  apply congrArg (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions.rationalH1Equiv IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B c)
  apply Subtype.ext
  exact hb i

theorem h1Pullback_comp {A B C : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) (g : B.toOver ⟶ C.toOver) :
    AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (f ≫ g) =
      (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f).comp (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g) := by
  have h := (AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) 1).map_comp g.op f.op
  exact congrArg (fun k => k.hom) h

/-- Equal marked matrices force the actual marked algebraic group map
to commute with the specified algebraic endomorphisms. -/
theorem marked_map_equivariant {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B)
    (f : A.toOver ⟶ B.toOver) [IsMonHom f]
    (hmark : ∀ z : Index → ℂ,
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f
        (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap a z))) =
          AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z)))
    (u : A.toOver ⟶ A.toOver) (v : B.toOver ⟶ B.toOver)
    [IsMonHom u] [IsMonHom v]
    (hmatrix : MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism a u = MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism b v) :
    u ≫ f = f ≫ v := by
  apply Faithfulness.Abelian.IntrinsicPeriods.algebraic_group_map_eq_of_h1Pullback_eq
  rw [h1Pullback_comp, h1Pullback_comp]
  apply LinearMap.ext
  intro c
  apply (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a).injective
  change MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a
      (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback u (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f c)) =
    MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback v c))
  rw [rationalCoordinates_pullback_of_marked_map a b f hmark]
  have h := LinearMap.congr_fun hmatrix (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b c)
  change MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback u
      ((MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a).symm (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b c))) =
    MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback v
      ((MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).symm (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b c))) at h
  rw [LinearEquiv.symm_apply_apply] at h
  rw [← rationalCoordinates_pullback_of_marked_map a b f hmark c,
    LinearEquiv.symm_apply_apply] at h
  exact h

end

/-!
Integral marked matrices of actual algebraic group morphisms. Integrality
is derived from their native linear lifts preserving the true period
lattices, not imposed on a rational H¹ action.
-/

open _root_.CategoryTheory OAI.Geometry.ComplexTorus.BettiLattice.CM.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod.Constructions.LatticeDual
open scoped BigOperators
open scoped _root_.Topology

variable {Index : Type} [Fintype Index]

def algebraicLinearLift {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) [IsMonHom f] : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B :=
  (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraic_map_linear_lift f).choose

theorem algebraicLinearLift_preservesLattice {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    Geometry.ComplexTorus.BettiLattice.CM.Construction.PreservesLattice (A := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A) (B := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B) (algebraicLinearLift f) :=
  (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraic_map_linear_lift f).choose_spec.1.1

theorem algebraicLinearLift_lifts {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    Geometry.ComplexTorus.BettiLattice.CM.Construction.Lifts (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraicTorusMap f) (algebraicLinearLift f) :=
  (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraic_map_linear_lift f).choose_spec.1.2

def algebraicLatticeMap {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) [IsMonHom f] : AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A →ₗ[ℤ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B :=
  (((algebraicLinearLift f).restrictScalars ℤ).domRestrict (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).codRestrict
    (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) (fun v =>
      algebraicLinearLift_preservesLattice f (v : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) v.property)

theorem rationalH1Equiv_lattice_sum {B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B)
    (c : B.variety.rationalCohomology 1) (l : AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) :
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions.rationalH1Equiv IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B c (AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod.Constructions.LatticeDual.latticeInclusion (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) l) =
      ∑ i, (b.repr l i : ℚ) * MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b c i := by
  let φ := (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions.rationalH1Equiv IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B c).toAddMonoidHom.comp
    (AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod.Constructions.LatticeDual.latticeInclusion (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B))
  have h := congrArg φ (b.sum_repr l)
  change φ l = _
  rw [← h, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, zsmul_eq_mul]
  rfl

theorem rationalCoordinates_algebraic_pullback {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B)
    (f : A.toOver ⟶ B.toOver) [IsMonHom f]
    (c : B.variety.rationalCohomology 1) (j : Index) :
    MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f c) j =
      ∑ i, (b.repr (algebraicLatticeMap f (a j)) i : ℚ) * MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b c i := by
  rw [MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates_apply,
    Faithfulness.Abelian.IntrinsicPeriods.rationalH1Equiv_algebraic_pullback f (algebraicLinearLift f)
      (algebraicLinearLift_preservesLattice f) (algebraicLinearLift_lifts f)]
  exact rationalH1Equiv_lattice_sum b c (algebraicLatticeMap f (a j))

/-- Every entry of the actual marked cohomological endomorphism matrix
is an integer, with the precise transpose convention fixed. -/
theorem markedEndomorphism_integer_entry {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (f : A.toOver ⟶ A.toOver) [IsMonHom f] (i j : Index) :
    MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism b f ((Pi.basisFun ℚ Index) i) j =
      (b.repr (algebraicLatticeMap f (b j)) i : ℚ) := by
  classical
  change MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f
    ((MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates b).symm ((Pi.basisFun ℚ Index) i))) j = _
  rw [rationalCoordinates_algebraic_pullback b b f]
  simp only [LinearEquiv.apply_symm_apply, Pi.basisFun_apply, Pi.single_apply]
  simp

/-- Continuity of the genuine rational matrices, viewed as real matrices,
forces local constancy because their entries were proved integral. -/
theorem markedEndomorphism_eventually_eq_of_continuous
    {S : Type} [TopologicalSpace S]
    (A : S → AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ∀ s, MarkedAbelianPeriods.IntrinsicPeriods.Marking Index (A s))
    (g : ∀ s, (A s).toOver ⟶ (A s).toOver) (hg : ∀ s, IsMonHom (g s))
    (s₀ : S)
    (hcont : ∀ i j, ContinuousAt
      (fun s => (MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s) (g s) ((Pi.basisFun ℚ Index) i) j : ℝ)) s₀) :
    ∀ᶠ s in 𝓝 s₀, MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s) (g s) = MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s₀) (g s₀) := by
  let (s : S) : IsMonHom (g s) := hg s
  have hentry (i j : Index) : ∀ᶠ s in 𝓝 s₀,
      (b s).repr (algebraicLatticeMap (g s) (b s j)) i =
        (b s₀).repr (algebraicLatticeMap (g s₀) (b s₀ j)) i := by
    let m := fun s => (b s).repr (algebraicLatticeMap (g s) (b s j)) i
    have hmreal : ContinuousAt (fun s => (m s : ℝ)) s₀ := by
      convert hcont i j using 1
      ext s
      rw [markedEndomorphism_integer_entry]
      simp only [Rat.cast_intCast]
      rfl
    have hm : ContinuousAt m s₀ :=
      Int.isClosedEmbedding_coe_real.isEmbedding.isInducing.continuousAt_iff.mpr hmreal
    exact hm.eventually ((isOpen_discrete {m s₀}).mem_nhds (Set.mem_singleton (m s₀)))
  have hall : ∀ᶠ s in 𝓝 s₀, ∀ i j,
      (b s).repr (algebraicLatticeMap (g s) (b s j)) i =
        (b s₀).repr (algebraicLatticeMap (g s₀) (b s₀ j)) i := by
    simpa only [Filter.eventually_all] using hentry
  filter_upwards [hall] with s hs
  apply (Pi.basisFun ℚ Index).ext
  intro i
  funext j
  rw [markedEndomorphism_integer_entry, markedEndomorphism_integer_entry, hs i j]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.IntegralMarkedMaps.Abelian.IntrinsicPeriods
