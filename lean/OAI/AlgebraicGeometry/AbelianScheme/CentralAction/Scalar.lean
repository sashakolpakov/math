import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Marking
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Descent

/-! # Scalar -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Scalar.Construction

noncomputable section

/-! The scalar's exact norm and residue congruence imply the actual PEL
polarization, action, and marking equations, on every test scheme. The
geometric finiteness/flatness of a scalar isogeny is separate from these
equations and is not replaced by a finite-order assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies

universe u

theorem scalar_natCast_schemeMap {S : Scheme.{u}} (A : Over S)
    [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    TateComparison.End.endSchemeMap A (n : TateComparison.End.IntegralEnd A) = (𝟙 A) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, TateComparison.BaseChange.endSchemeMap_add, ih, TateComparison.BaseChange.endSchemeMap_one, pow_succ]

variable {E : Type u} [Field E] [NumberField E] [NumberField.IsCMField E]
  {g N : ℕ} {S : Scheme.{u}}

def scalarMap (D : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
    (b : NumberField.RingOfIntegers E) : D.abelian.scheme ⟶ D.abelian.scheme :=
  TateComparison.End.endSchemeMap D.abelian.scheme (D.action b)

instance scalarMap_isMonHom
    (D : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
    (b : NumberField.RingOfIntegers E) : IsMonHom (scalarMap D b) :=
  TateComparison.End.endSchemeMap_isMonHom _ _

omit [NumberField E] [NumberField.IsCMField E] in
/-- Congruence to one fixes every N-torsion point, uniformly in the test
scheme; hence it fixes the full marking rather than only its geometric fiber. -/
theorem scalarMap_fixes_torsion
    (D : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
    (b : NumberField.RingOfIntegers E) (hlevel : Marking.Construction.levelReduction E N b = 1)
    (T : Over S) (x : T ⟶ D.abelian.scheme) (hx : x ^ N = 1) :
    x ≫ scalarMap D b = x := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ((Marking.Construction.level_eq_one_iff E N b).mp hlevel)
  have hb : b = 1 + r * (N : NumberField.RingOfIntegers E) := by
    rw [mul_comm r, ← hr]
    abel
  unfold scalarMap
  rw [hb, map_add, map_one, TateComparison.BaseChange.endSchemeMap_add, TateComparison.BaseChange.endSchemeMap_one,
    MonObj.comp_mul, Category.comp_id, map_mul, TateComparison.BaseChange.endSchemeMap_mul, map_natCast,
    scalar_natCast_schemeMap, ← Category.assoc, MonObj.comp_pow, Category.comp_id,
    hx, MonObj.one_comp, mul_one]

omit [NumberField E] [NumberField.IsCMField E] in
theorem scalarMap_fixes_full_marking
    (D : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
    (b : NumberField.RingOfIntegers E) (hlevel : Marking.Construction.levelReduction E N b = 1)
    (T : Over S)
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    (D.marking.hom.app (.op T) c).val ≫ scalarMap D b =
      (D.marking.hom.app (.op T) c).val :=
  scalarMap_fixes_torsion D b hlevel T _ (D.marking.hom.app (.op T) c).property

/-- Rosati compatibility turns b * conjugate(b) = n into the precise
pullback polarization equation for the actual scalar endomorphism. -/
theorem scalarMap_polarization
    (D : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
    (hRosati : D.IsRosatiCompatible
      (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom)
    (b : NumberField.RingOfIntegers E) (n : ℕ)
    (hnorm : b * NumberField.IsCMField.ringOfIntegersComplexConj E b = n) :
    ∃ bd : TateComparison.End.IntegralEnd D.dual.abelian.scheme,
      D.IsPoincareDual (D.action b) bd ∧
      scalarMap D b ≫ D.polarizationMap.hom ≫
        TateComparison.End.endSchemeMap D.dual.abelian.scheme bd = D.polarizationMap.hom ^ n := by
  obtain ⟨bd, hdual, hRos⟩ := hRosati b
  refine ⟨bd, hdual, ?_⟩
  rw [hRos]
  unfold scalarMap
  rw [← Category.assoc, ← TateComparison.BaseChange.endSchemeMap_mul, ← map_mul]
  change TateComparison.End.endSchemeMap D.abelian.scheme
    (D.action (NumberField.IsCMField.ringOfIntegersComplexConj E b * b)) ≫
      D.polarizationMap.hom = D.polarizationMap.hom ^ n
  rw [mul_comm _ b, hnorm, map_natCast, scalar_natCast_schemeMap,
    MonObj.pow_comp, Category.id_comp]

/-- Once the scalar map is known to be a finite flat surjection, the
principalization equations construct its full polarized marked isogeny.
Every compatibility field is proved here from the ordinary PEL axioms. -/
def scalarPELIsogeny
    (D : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
    (hRosati : D.IsRosatiCompatible
      (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom)
    (b : NumberField.RingOfIntegers E) (n : ℕ)
    (hnorm : b * NumberField.IsCMField.ringOfIntegersComplexConj E b = n)
    (hlevel : Marking.Construction.levelReduction E N b = 1)
    [IsFinite (scalarMap D b).left] [Flat (scalarMap D b).left]
    [Surjective (scalarMap D b).left] : TateComparison.PELIsogenies.PELIsogeny D D n :=
  let h := scalarMap_polarization D hRosati b n hnorm
  { isogeny := {
      hom := scalarMap D b
      preservesGroup := inferInstance
      finite := inferInstance
      flat := inferInstance
      surjective := inferInstance }
    dualHom := TateComparison.End.endSchemeMap D.dual.abelian.scheme h.choose
    dualGroup := inferInstance
    poincare := h.choose_spec.1
    equivariant := by
      intro r
      unfold scalarMap
      rw [← TateComparison.BaseChange.endSchemeMap_mul, ← TateComparison.BaseChange.endSchemeMap_mul, ← map_mul, ← map_mul, mul_comm]
    polarization := h.choose_spec.2
    marking := scalarMap_fixes_full_marking D b hlevel }

/-- The complementary scalar is conjugation, with exact multiplication
by the prescribed norm in both composition orders. -/
theorem scalarMap_complements
    (D : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
    (b : NumberField.RingOfIntegers E) (n : ℕ)
    (hnorm : b * NumberField.IsCMField.ringOfIntegersComplexConj E b = n) :
    scalarMap D b ≫ scalarMap D (NumberField.IsCMField.ringOfIntegersComplexConj E b) =
        (𝟙 D.abelian.scheme) ^ n ∧
      scalarMap D (NumberField.IsCMField.ringOfIntegersComplexConj E b) ≫ scalarMap D b =
        (𝟙 D.abelian.scheme) ^ n := by
  unfold scalarMap
  constructor
  · rw [← TateComparison.BaseChange.endSchemeMap_mul, ← map_mul, mul_comm _ b, hnorm, map_natCast,
      scalar_natCast_schemeMap]
  · rw [← TateComparison.BaseChange.endSchemeMap_mul, ← map_mul, hnorm, map_natCast, scalar_natCast_schemeMap]

/-- Finite etaleness of multiplication by the scalar norm supplies all
the geometric isogeny properties; none are stored as scalar-action data. -/
def scalarPELIsogeny_of_finiteEtale_multiplier
    (D : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
    (hRosati : D.IsRosatiCompatible
      (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom)
    (b : NumberField.RingOfIntegers E) (n : ℕ)
    (hnorm : b * NumberField.IsCMField.ringOfIntegersComplexConj E b = n)
    (hlevel : Marking.Construction.levelReduction E N b = 1)
    [IsFinite ((𝟙 D.abelian.scheme) ^ n).left]
    [Etale ((𝟙 D.abelian.scheme) ^ n).left]
    [Surjective ((𝟙 D.abelian.scheme) ^ n).left] : TateComparison.PELIsogenies.PELIsogeny D D n := by
  let f := scalarMap D b
  let g := scalarMap D (NumberField.IsCMField.ringOfIntegersComplexConj E b)
  have hSeparated (a : D.abelian.scheme ⟶ D.abelian.scheme) : IsSeparated a.left := by
    have hcomp : IsSeparated (a.left ≫ D.abelian.scheme.hom) := by
      rw [a.w]
      infer_instance
    exact IsSeparated.of_comp a.left D.abelian.scheme.hom
  have : IsSeparated f.left := hSeparated f
  have : IsSeparated g.left := hSeparated g
  have hc := scalarMap_complements D b n hnorm
  have hh := Descent.Construction.finite_etale_surjective_of_complements f.left g.left
    ((𝟙 D.abelian.scheme) ^ n).left
    (congrArg Over.Hom.left hc.1) (congrArg Over.Hom.left hc.2)
  have : IsFinite (scalarMap D b).left := hh.1
  have : Etale (scalarMap D b).left := hh.2.1
  have : Surjective (scalarMap D b).left := hh.2.2
  exact scalarPELIsogeny D hRosati b n hnorm hlevel

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Scalar.Construction
