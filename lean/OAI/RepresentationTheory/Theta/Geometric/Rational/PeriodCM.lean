import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodEq
import OAI.RepresentationTheory.Theta.Geometric.AwayLattice
import OAI.RepresentationTheory.Theta.Geometric.Torus.Hom

/-! # Period CM -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Geometric

/-! The actual rational matrix induces a linear map between the explicit
period quotients. Clearing its reference lattice denominators makes this
an integral map of their period tori. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.rationalPeriodLinear (g : D.RationalSU) (x : D.domain) :
    Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) →ₗ[ℂ] Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) :=
  (D.periodProjection (D.periodMap g x.val)).comp
    ((D.rationalAmbient g).toLinearMap.comp D.periodSection)

theorem Data.ActiveHeckeThetaData.rationalPeriodLinear_projection (hg : D.pel.HasIntegralModelGeometry)
    (g : D.RationalSU) (x : D.domain) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    D.rationalPeriodLinear g x (D.periodProjection x.val u) =
      D.periodProjection (D.periodMap g x.val) (D.rationalAmbient g u) := by
  let y : D.domain := ⟨D.periodMap g x.val, D.periodMap_preserves g x.val x.property⟩
  have hk : D.periodSection (D.periodProjection x.val u) - u ∈ D.pel.reference.periodFamily x.val := by
    rw [← D.periodProjection_kernel hg x]
    change D.periodProjection x.val (_ - _) = 0
    rw [map_sub, D.periodProjection_section hg, sub_self]
  have hkg := D.rationalAmbient_period_kernel hg g x _ hk
  rw [← D.periodProjection_kernel hg y] at hkg
  change D.periodProjection y.val (D.rationalAmbient g (_ - _)) = 0 at hkg
  rw [map_sub, map_sub, sub_eq_zero] at hkg
  exact hkg

theorem Data.ActiveHeckeThetaData.rationalPeriodLinear_reference (hg : D.pel.HasIntegralModelGeometry)
    (g : D.RationalSU) (x : D.domain) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    D.rationalPeriodLinear g x (D.periodReferenceEmbedding x.val v) =
      D.periodReferenceEmbedding (D.periodMap g x.val) (D.rationalLinear g v) := by
  change D.rationalPeriodLinear g x (D.periodProjection x.val _) = D.periodProjection _ _
  rw [D.rationalPeriodLinear_projection hg, D.rationalAmbient_embedding]

theorem Data.ActiveHeckeThetaData.cleared_rationalPeriodLinear_integral (hg : D.pel.HasIntegralModelGeometry)
    (g : D.RationalSU) (n : ℕ)
    (hn : ∀ v ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v ∈ D.pel.reference.lattice)
    (x : D.domain) (t : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) (ht : t ∈ D.periodLattice x.val) :
    ((q : ℤ) ^ n • D.rationalPeriodLinear g x) t ∈ D.periodLattice (D.periodMap g x.val) := by
  obtain ⟨v, hv, rfl⟩ := (D.periodLattice_mem x.val t).mp ht
  change (q : ℤ) ^ n • D.rationalPeriodLinear g x (D.periodReferenceEmbedding x.val v) ∈ _
  rw [D.rationalPeriodLinear_reference hg, ← map_zsmul]
  exact (D.periodLattice_mem _ _).mpr ⟨_, hn v hv, rfl⟩

theorem Data.ActiveHeckeThetaData.exists_cleared_rationalPeriodLinear (hg : D.pel.HasIntegralModelGeometry)
    (hc : D.HasFiniteCoordinates) (g : D.RationalSU) (ha : D.away g ∈ D.awayLevel) :
    ∃ n : ℕ, ∀ (x : D.domain) t, t ∈ D.periodLattice x.val →
      ((q : ℤ) ^ n • D.rationalPeriodLinear g x) t ∈ D.periodLattice (D.periodMap g x.val) := by
  obtain ⟨n, hn⟩ := D.away_level_clears_lattice hg hc g ha
  exact ⟨n, D.cleared_rationalPeriodLinear_integral hg g n hn⟩

end RepresentationTheory.Theta.Geometric

namespace RepresentationTheory.Theta.Geometric.Rational.PeriodCM.ActiveHeckeThetaData
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open scoped _root_.Manifold
section

/-! Cleared rational SU maps are actual holomorphic maps between the
explicit period tori, and algebraize between their abelian models. -/

open scoped ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.rationalPeriodPoint (g : D.RationalSU) (x : D.domain) : D.domain :=
  ⟨D.periodMap g x.val, D.periodMap_preserves g x.val x.property⟩

def _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.clearedPeriodTorusMap (hg : D.pel.HasIntegralModelGeometry) (g : D.RationalSU) (n : ℕ)
    (hn : ∀ v ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v ∈ D.pel.reference.lattice)
    (x : D.domain) : (D.canonicalPeriodData hg x).periodTorus →+
      (D.canonicalPeriodData hg (D.rationalPeriodPoint g x)).periodTorus :=
  Torus.Hom.torusLinearMap (D.canonicalPeriodData hg x)
    (D.canonicalPeriodData hg (D.rationalPeriodPoint g x))
    ((q : ℤ) ^ n • D.rationalPeriodLinear g x)
    (D.cleared_rationalPeriodLinear_integral hg g n hn x)

@[simp] theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.clearedPeriodTorusMap_mk (hg : D.pel.HasIntegralModelGeometry) (g : D.RationalSU) (n : ℕ)
    (hn : ∀ v ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v ∈ D.pel.reference.lattice)
    (x : D.domain) (t : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    D.clearedPeriodTorusMap hg g n hn x (QuotientAddGroup.mk t) =
      QuotientAddGroup.mk ((q : ℤ) ^ n • D.rationalPeriodLinear g x t) := rfl

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.exists_algebraic_cleared_period_map (hg : D.pel.HasIntegralModelGeometry)
    (g : D.RationalSU) (n : ℕ)
    (hn : ∀ v ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v ∈ D.pel.reference.lattice)
    (x : D.domain) (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (eA : (D.canonicalPeriodData hg x).periodTorus ≃ₘ⟮
      𝓘(ℂ, (D.canonicalPeriodData hg x).space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (eB : (D.canonicalPeriodData hg (D.rationalPeriodPoint g x)).periodTorus ≃ₘ⟮
      𝓘(ℂ, (D.canonicalPeriodData hg (D.rationalPeriodPoint g x)).space),
      𝓘(ℂ, AlgebraicAction.AbelianModel B)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
    (hA : ∀ u v, eA (u + v) = eA u * eA v)
    (hB : ∀ u v, eB (u + v) = eB u * eB v) :
    ∃ f : A.toOver ⟶ B.toOver, IsMonHom f ∧
      ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (eA t) = eB (D.clearedPeriodTorusMap hg g n hn x t) :=
  Torus.Hom.exists_algebraic_torus_map (D.canonicalPeriodData hg x)
    (D.canonicalPeriodData hg (D.rationalPeriodPoint g x))
    ((q : ℤ) ^ n • D.rationalPeriodLinear g x)
    (D.cleared_rationalPeriodLinear_integral hg g n hn x) A B eA eB hA hB

end

/-! The actual cleared rational maps intertwine the CM actions, first on
the period quotients and then on their algebraic abelian models. -/

open scoped ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.rationalAmbient_scalar (g : D.RationalSU) (a : E) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    D.rationalAmbient g (NumberTheory.ArithmeticGroups.Action.CongruenceLevel.ambientAction D.pel.reference.embeddings a u) =
      NumberTheory.ArithmeticGroups.Action.CongruenceLevel.ambientAction D.pel.reference.embeddings a (D.rationalAmbient g u) := by
  funext i
  apply Prod.ext
  · exact map_smul (D.rationalAtEmbedding (D.pel.reference.embeddings i).toRingHom g) _ _
  · exact map_smul (D.rationalAtEmbedding (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (D.pel.reference.embeddings i)).toRingHom g) _ _

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.rationalPeriodLinear_scalar (hg : D.pel.HasIntegralModelGeometry)
    (g : D.RationalSU) (x : D.domain) (a : E) (t : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    D.rationalPeriodLinear g x (D.periodScalarAction a t) =
      D.periodScalarAction a (D.rationalPeriodLinear g x t) := by
  have hs := D.periodProjection_section hg x.val t
  calc
    D.rationalPeriodLinear g x (D.periodScalarAction a t) =
        D.rationalPeriodLinear g x (D.periodProjection x.val
          (NumberTheory.ArithmeticGroups.Action.CongruenceLevel.ambientAction D.pel.reference.embeddings a (D.periodSection t))) := by
      rw [D.periodProjection_ambientAction, hs]
    _ = D.periodProjection (D.periodMap g x.val)
        (D.rationalAmbient g (NumberTheory.ArithmeticGroups.Action.CongruenceLevel.ambientAction D.pel.reference.embeddings a (D.periodSection t))) :=
      D.rationalPeriodLinear_projection hg g x _
    _ = D.periodScalarAction a (D.rationalPeriodLinear g x t) := by
      rw [D.rationalAmbient_scalar, D.periodProjection_ambientAction]
      rfl

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.clearedPeriodTorusMap_CM (hg : D.pel.HasIntegralModelGeometry) (g : D.RationalSU) (n : ℕ)
    (hn : ∀ v ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v ∈ D.pel.reference.lattice)
    (x : D.domain) (a : NumberField.RingOfIntegers E)
    (t : (D.canonicalPeriodData hg x).periodTorus) :
    D.clearedPeriodTorusMap hg g n hn x (D.canonicalQuotientAction hg x a t) =
      D.canonicalQuotientAction hg (D.rationalPeriodPoint g x) a
        (D.clearedPeriodTorusMap hg g n hn x t) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
  change QuotientAddGroup.mk ((q : ℤ) ^ n • D.rationalPeriodLinear g x (D.periodScalarAction (a : E) v)) =
    QuotientAddGroup.mk (D.periodScalarAction (a : E) ((q : ℤ) ^ n • D.rationalPeriodLinear g x v))
  have h : (q : ℤ) ^ n • D.rationalPeriodLinear g x (D.periodScalarAction (a : E) v) =
      D.periodScalarAction (a : E) ((q : ℤ) ^ n • D.rationalPeriodLinear g x v) :=
    (congrArg (fun t : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) => (q : ℤ) ^ n • t)
      (D.rationalPeriodLinear_scalar hg g x (a : E) v)).trans
      (map_zsmul (D.periodScalarAction (a : E)) ((q : ℤ) ^ n) (D.rationalPeriodLinear g x v)).symm
  exact congrArg (QuotientAddGroup.mk : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) →
    Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) ⧸ D.periodLattice (D.periodMap g x.val)) h

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper A.toOver.hom :=
  A.variety.presentation.projective.isProper

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.algebraic_cleared_period_map_CM (hg : D.pel.HasIntegralModelGeometry)
    (g : D.RationalSU) (n : ℕ)
    (hn : ∀ v ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v ∈ D.pel.reference.lattice)
    (x : D.domain) (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (eA : (D.canonicalPeriodData hg x).periodTorus ≃ₘ⟮
      𝓘(ℂ, (D.canonicalPeriodData hg x).space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (eB : (D.canonicalPeriodData hg (D.rationalPeriodPoint g x)).periodTorus ≃ₘ⟮
      𝓘(ℂ, (D.canonicalPeriodData hg (D.rationalPeriodPoint g x)).space),
      𝓘(ℂ, AlgebraicAction.AbelianModel B)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
    (rA : NumberField.RingOfIntegers E →+* AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A.toOver)
    (rB : NumberField.RingOfIntegers E →+* AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd B.toOver)
    (hA : ∀ a t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A.toOver (rA a)) (eA t) =
      eA (D.canonicalQuotientAction hg x a t))
    (hB : ∀ a t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap B.toOver (rB a)) (eB t) =
      eB (D.canonicalQuotientAction hg (D.rationalPeriodPoint g x) a t))
    (f : A.toOver ⟶ B.toOver)
    (hf : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (eA t) = eB (D.clearedPeriodTorusMap hg g n hn x t))
    (a : NumberField.RingOfIntegers E) :
    AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A.toOver (rA a) ≫ f = f ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap B.toOver (rB a) := by
  apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points
  intro p
  obtain ⟨t, rfl⟩ := eA.surjective p
  have hA' (t) : eA t ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A.toOver (rA a) = eA (D.canonicalQuotientAction hg x a t) := hA a t
  have hB' (t) : eB t ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap B.toOver (rB a) =
      eB (D.canonicalQuotientAction hg (D.rationalPeriodPoint g x) a t) := hB a t
  have hf' (t) : eA t ≫ f = eB (D.clearedPeriodTorusMap hg g n hn x t) := hf t
  calc
    eA t ≫ (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A.toOver (rA a) ≫ f) =
        (eA t ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A.toOver (rA a)) ≫ f := (Category.assoc _ _ _).symm
    _ = eA (D.canonicalQuotientAction hg x a t) ≫ f := congrArg (fun p => p ≫ f) (hA' t)
    _ = eB (D.clearedPeriodTorusMap hg g n hn x (D.canonicalQuotientAction hg x a t)) := hf' _
    _ = eB (D.canonicalQuotientAction hg (D.rationalPeriodPoint g x) a
        (D.clearedPeriodTorusMap hg g n hn x t)) := congrArg eB (D.clearedPeriodTorusMap_CM hg g n hn x a t)
    _ = eB (D.clearedPeriodTorusMap hg g n hn x t) ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap B.toOver (rB a) := (hB' _).symm
    _ = (eA t ≫ f) ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap B.toOver (rB a) :=
      congrArg (fun p => p ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap B.toOver (rB a)) (hf' t).symm
    _ = eA t ≫ (f ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap B.toOver (rB a)) := Category.assoc _ _ _

end RepresentationTheory.Theta.Geometric.Rational.PeriodCM.ActiveHeckeThetaData

end

end OAI
