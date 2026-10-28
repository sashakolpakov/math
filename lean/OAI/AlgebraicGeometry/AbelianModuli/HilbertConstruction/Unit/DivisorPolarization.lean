import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.DivisorPolarization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.DividedPolarizationSymmetry

/-! # Divisor Polarization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A divisor of an inducing homomorphism gives the original polarization
when its graph power is the normalized ample line and the dividing integer
is invertible on the base. The constructions include arbitrary test-scheme
base changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

/-- The graph comparison supplies an ample graph line; invertible
divisibility supplies symmetry and excludes characteristic two. -/
theorem Unit.DivisorPolarization.positiveFormula_of_unit_divisor_graphPower
    {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
    (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
    (d : ℕ) (hd : 0 < d) (hunit : IsUnit ((2 * d : ℕ) : Γ(Spec (.of K), ⊤)))
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsAmple)
    (e : (((D.poincareAt m).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)
    (hp : A.multiplication (2 * d) ≫ p = m)
    (eG : (A.zeroNormalizedBundle L).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower d).sheaf) :
    AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A.scheme (D.poincareAt p) := by
  have hG : (PoincareGraph.Bundles.poincareGraphBundle D p).IsAmple :=
    Line.Bundles.LineBundle.IsAmple.of_tensorPower d hd
      ((Rational.DivisorPolarization.zeroNormalizedBundle_isAmple_overField A L hL).of_iso eG)
  have hs : ∀ x y : A.scheme ⊗ A.scheme ⟶ A.scheme,
      D.poincarePairClass (A.scheme ⊗ A.scheme) (x ≫ p) y =
        D.poincarePairClass (A.scheme ⊗ A.scheme) (y ≫ p) x := by
    intro x y
    exact Unit.DividedPolarizationSymmetry.unit_divisor_pair_symmetric D p (2 * d) hunit m L e hp x y
  have hprod : IsUnit ((2 * d : ℕ) : K) := by
    simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of K)).hom.hom
  have h2 : (2 : K) ≠ 0 := by
    intro hzero
    apply hprod.ne_zero
    simp only [Nat.cast_mul, Nat.cast_ofNat, hzero, zero_mul]
  exact SymmetricAmpleGraphPositivity.positiveFormula_of_symmetric_ample_graph D p hs h2 hG

/-- The original positivity condition on a geometric fiber, using the
actual pullback of the inducing line and the actual graph comparison. -/
theorem Unit.DivisorPolarization.positiveOnGeometricFiber_of_unit_divisor_graphPower
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
    (d : ℕ) (hd : 0 < d) (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (e : (((D.poincareAt m).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)
    (hp : A.multiplication (2 * d) ≫ p = m)
    (eG : (A.zeroNormalizedBundle L).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower d).sheaf)
    (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S)
    (hL : (L.pullback (pullback.fst A.scheme.hom s)).IsAmple) :
    PolarizationData.PositiveOnGeometricFiber D p K s := by
  let B := A.pullback s
  let E := D.pullback s
  let p' : B.scheme ⟶ E.abelian.scheme := (Over.pullback s).map p
  let : IsMonHom p' :=
    Functor.map.instIsMonHom (F := Over.pullback s) (f := p) A.scheme D.abelian.scheme
  let m' : B.scheme ⟶ E.abelian.scheme := (Over.pullback s).map m
  let q : B.scheme.left ⟶ A.scheme.left := pullback.fst A.scheme.hom s
  let L' : Line.Bundles.LineBundle B.scheme.left := L.pullback q
  have hp' : B.multiplication (2 * d) ≫ p' = m' :=
    (congrArg (fun z : B.scheme ⟶ B.scheme => z ≫ p')
      (A.multiplication_baseChange s (2 * d)).symm).trans
        (((Over.pullback s).map_comp (A.multiplication (2 * d)) p).symm.trans
          (congrArg (Over.pullback s).map hp))
  let eG' : (B.zeroNormalizedBundle L').sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle E p').tensorPower d).sheaf :=
    (A.zeroNormalizedBundle_baseChangeIso L s).symm ≪≫
      (Scheme.Modules.pullback q).mapIso eG ≪≫
      (PoincareGraph.Bundles.poincareGraphBundle D p).powerBaseChangeIso q d ≪≫
      (TensorPower.Maps.tensorPowerFunctor _ d).mapIso (PoincareGraph.Bundles.poincareGraphBundle_baseChangeIso D p s).symm
  have hpos := Unit.DivisorPolarization.positiveFormula_of_unit_divisor_graphPower E p' d hd
    (Abelian.Schemes.level_unit_under_base_change s (2 * d) hunit)
    m' L' hL (Rational.DivisorPolarization.inducingFormulaBaseChangeIso D m L e s) hp' eG'
  exact Picard.PoincareBundle.PositiveFormulaIsomorphism.of_iso B.scheme
    (E.poincareAt p') (PolarizationData.polarizationBiextensionAt D p s)
    (Polarization.BiextensionPoincarePoint.polarizationBiextensionAt_poincareAtIso D p s) hpos

/-- Assemble the original polarization from its isogeny and kernel type,
with positivity proved from the relatively ample graph power. -/
def PolarizationData.Polarization.ofUnitDivisorGraphPower
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (d : ℕ) (hd : 0 < d) (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsRelativelyAmple A.scheme.hom)
    (e : (((D.poincareAt m).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)
    (hp : A.multiplication (2 * d) ≫ p.hom = m)
    (eG : (A.zeroNormalizedBundle L).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle D p.hom).tensorPower d).sheaf) : PolarizationData.Polarization D δ where
  isogeny := p
  kernelType := hδ
  positive K _ _ s := Unit.DivisorPolarization.positiveOnGeometricFiber_of_unit_divisor_graphPower
    D p.hom d hd hunit m L e hp eG K s
      (hL.isAmple_after_affine_cartesian (IsPullback.of_hasPullback A.scheme.hom s))

/-- Absolute ampleness suffices when the dividing integer is a unit. -/
def PolarizationData.Polarization.ofAmpleUnitDivisorGraphPower
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (d : ℕ) (hd : 0 < d) (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsAmple)
    (e : (((D.poincareAt m).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)
    (hp : A.multiplication (2 * d) ≫ p.hom = m)
    (eG : (A.zeroNormalizedBundle L).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle D p.hom).tensorPower d).sheaf) : PolarizationData.Polarization D δ where
  isogeny := p
  kernelType := hδ
  positive K _ _ s := by
    let : IsAffineHom s := Quotients.FiniteDescent.LineTrivializationOf.Construction.LineTrivialization.isAffineHom_from_field s
    let : IsAffineHom (pullback.fst A.scheme.hom s) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom)
        (IsPullback.of_hasPullback A.scheme.hom s).flip (inferInstance : IsAffineHom s)
    exact Unit.DivisorPolarization.positiveOnGeometricFiber_of_unit_divisor_graphPower
      D p.hom d hd hunit m L e hp eG K s
        (hL.pullback_of_isAffineHom (pullback.fst A.scheme.hom s))

/-- A divisor and graph comparison on any test-scheme base change of an
ample affine-base family give a polarization on that test scheme. -/
def PolarizationData.Polarization.ofBaseChangedUnitDivisorGraphPower
    {S T : Scheme} [IsAffine S] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (b : T ⟶ S)
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback b) (D.abelian.pullback b))
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (d : ℕ) (hd : 0 < d) (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsAmple)
    (e : (((D.poincareAt m).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)
    (hp : (A.pullback b).multiplication (2 * d) ≫ p.hom = (Over.pullback b).map m)
    (eG : ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom b)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback b) p.hom).tensorPower d).sheaf) :
    PolarizationData.Polarization (D.pullback b) δ :=
  PolarizationData.Polarization.ofUnitDivisorGraphPower (D.pullback b) p δ hδ d hd
    (Abelian.Schemes.level_unit_under_base_change b (2 * d) hunit)
    ((Over.pullback b).map m) (L.pullback (pullback.fst A.scheme.hom b))
    (hL.relativelyAmple_after_baseChange (IsPullback.of_hasPullback A.scheme.hom b))
    (Rational.DivisorPolarization.inducingFormulaBaseChangeIso D m L e b) hp
    ((A.zeroNormalizedBundle_baseChangeIso L b).symm ≪≫ eG)

/-- Positivity from the inducing formula on the zero-normalized line.
Only the original line is required to be ample on this fiber. -/
theorem Unit.DivisorPolarization.positiveOnGeometricFiber_of_normalized_unit_divisor_graphPower
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
    (d : ℕ) (hd : 0 < d) (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (e : (((D.poincareAt m).tensor
      ((A.zeroNormalizedBundle L).pullback (fst A.scheme A.scheme).left)).tensor
      ((A.zeroNormalizedBundle L).pullback (snd A.scheme A.scheme).left)).sheaf ≅
        ((A.zeroNormalizedBundle L).pullback μ[A.scheme].left).sheaf)
    (hp : A.multiplication (2 * d) ≫ p = m)
    (eG : (A.zeroNormalizedBundle L).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle D p).tensorPower d).sheaf)
    (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S)
    (hL : (L.pullback (pullback.fst A.scheme.hom s)).IsAmple) :
    PolarizationData.PositiveOnGeometricFiber D p K s := by
  let a : (A.zeroNormalizedBundle (A.zeroNormalizedBundle L)).sheaf ≅
      (A.zeroNormalizedBundle L).sheaf :=
    Line.Bundles.LineBundle.sectionNormalized_fixedIso A.scheme.hom η[A.scheme].left
      (A.zeroNormalizedBundle L) ⟨A.zeroNormalizedBundle_zeroIso L⟩
  have hN : ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom s)).IsAmple :=
    (Rational.DivisorPolarization.zeroNormalizedBundle_isAmple_overField (A.pullback s)
      (L.pullback (pullback.fst A.scheme.hom s)) hL).of_iso
        (A.zeroNormalizedBundle_baseChangeIso L s).symm
  exact Unit.DivisorPolarization.positiveOnGeometricFiber_of_unit_divisor_graphPower
    D p d hd hunit m (A.zeroNormalizedBundle L) e hp (a ≪≫ eG) K s hN

/-- A relatively ample original line with its actual normalized inducing
formula gives the original polarization. -/
def PolarizationData.Polarization.ofNormalizedUnitDivisorGraphPower
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (d : ℕ) (hd : 0 < d) (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsRelativelyAmple A.scheme.hom)
    (e : (((D.poincareAt m).tensor
      ((A.zeroNormalizedBundle L).pullback (fst A.scheme A.scheme).left)).tensor
      ((A.zeroNormalizedBundle L).pullback (snd A.scheme A.scheme).left)).sheaf ≅
        ((A.zeroNormalizedBundle L).pullback μ[A.scheme].left).sheaf)
    (hp : A.multiplication (2 * d) ≫ p.hom = m)
    (eG : (A.zeroNormalizedBundle L).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle D p.hom).tensorPower d).sheaf) : PolarizationData.Polarization D δ where
  isogeny := p
  kernelType := hδ
  positive K _ _ s := Unit.DivisorPolarization.positiveOnGeometricFiber_of_normalized_unit_divisor_graphPower
    D p.hom d hd hunit m L e hp eG K s
      (hL.isAmple_after_affine_cartesian (IsPullback.of_hasPullback A.scheme.hom s))

/-- Absolute ampleness of the original line suffices for the normalized
inducing formula when the dividing integer is invertible. -/
def PolarizationData.Polarization.ofAmpleNormalizedUnitDivisorGraphPower
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (d : ℕ) (hd : 0 < d) (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsAmple)
    (e : (((D.poincareAt m).tensor
      ((A.zeroNormalizedBundle L).pullback (fst A.scheme A.scheme).left)).tensor
      ((A.zeroNormalizedBundle L).pullback (snd A.scheme A.scheme).left)).sheaf ≅
        ((A.zeroNormalizedBundle L).pullback μ[A.scheme].left).sheaf)
    (hp : A.multiplication (2 * d) ≫ p.hom = m)
    (eG : (A.zeroNormalizedBundle L).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle D p.hom).tensorPower d).sheaf) : PolarizationData.Polarization D δ where
  isogeny := p
  kernelType := hδ
  positive K _ _ s := by
    let : IsAffineHom s := Quotients.FiniteDescent.LineTrivializationOf.Construction.LineTrivialization.isAffineHom_from_field s
    let : IsAffineHom (pullback.fst A.scheme.hom s) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom)
        (IsPullback.of_hasPullback A.scheme.hom s).flip (inferInstance : IsAffineHom s)
    exact Unit.DivisorPolarization.positiveOnGeometricFiber_of_normalized_unit_divisor_graphPower
      D p.hom d hd hunit m L e hp eG K s
        (hL.pullback_of_isAffineHom (pullback.fst A.scheme.hom s))

/-- The raw normalized graph-power comparison on any test scheme is
enough; ampleness is required only on the original affine-base family. -/
def PolarizationData.Polarization.ofBaseChangedNormalizedUnitDivisorGraphPower
    {S T : Scheme} [IsAffine S] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (b : T ⟶ S)
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback b) (D.abelian.pullback b))
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (d : ℕ) (hd : 0 < d) (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsAmple)
    (e : (((D.poincareAt m).tensor
      ((A.zeroNormalizedBundle L).pullback (fst A.scheme A.scheme).left)).tensor
      ((A.zeroNormalizedBundle L).pullback (snd A.scheme A.scheme).left)).sheaf ≅
        ((A.zeroNormalizedBundle L).pullback μ[A.scheme].left).sheaf)
    (hp : (A.pullback b).multiplication (2 * d) ≫ p.hom = (Over.pullback b).map m)
    (eG : ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom b)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback b) p.hom).tensorPower d).sheaf) :
    PolarizationData.Polarization (D.pullback b) δ :=
  PolarizationData.Polarization.ofNormalizedUnitDivisorGraphPower (D.pullback b) p δ hδ d hd
    (Abelian.Schemes.level_unit_under_base_change b (2 * d) hunit)
    ((Over.pullback b).map m) (L.pullback (pullback.fst A.scheme.hom b))
    (hL.relativelyAmple_after_baseChange (IsPullback.of_hasPullback A.scheme.hom b))
    (Rational.DivisorPolarization.inducingFormulaLineIso (D.pullback b) ((Over.pullback b).map m)
      (A.zeroNormalizedBundle_baseChangeIso L b)
      (Rational.DivisorPolarization.inducingFormulaBaseChangeIso D m (A.zeroNormalizedBundle L) e b)) hp
    ((A.zeroNormalizedBundle_baseChangeIso L b).symm ≪≫ eG)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
