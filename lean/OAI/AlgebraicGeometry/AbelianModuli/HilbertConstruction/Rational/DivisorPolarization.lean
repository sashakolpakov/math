import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DividedPolarizationSymmetry
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SymmetricAmpleGraphPositivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.ZeroNormalizedBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BiextensionPoincarePoint
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Multiplication.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.AmpleAffineTest
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffineBaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineTrivializationOf
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.ProductBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveFormulaAffineSquare

/-! # Divisor Polarization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An actual rational divisor of an inducing homomorphism is a
polarization when its graph power is the normalized ample line.
The constructions retain the original geometric positivity and kernel
type, including on arbitrary test-scheme base changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

/-- Pull back the actual inducing tensor formula along any base change. -/
def Rational.DivisorPolarization.inducingFormulaBaseChangeIso
    {S T : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (m : A.scheme ⟶ D.abelian.scheme)
    (L : Line.Bundles.LineBundle A.scheme.left)
    (e : (((D.poincareAt m).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)
    (b : T ⟶ S) :
    let B := (A.pullback b).scheme
    let L' := L.pullback (pullback.fst A.scheme.hom b)
    ((((D.pullback b).poincareAt ((Over.pullback b).map m)).tensor
      (L'.pullback (fst B B).left)).tensor (L'.pullback (snd B B).left)).sheaf ≅
        (L'.pullback μ[B].left).sheaf := by
  let B := (A.pullback b).scheme
  let q : B.left ⟶ A.scheme.left := pullback.fst A.scheme.hom b
  let r : (B ⊗ B).left ⟶ (A.scheme ⊗ A.scheme).left :=
    Picard.PoincareBundle.Field.ProductBaseChange.productMap b A.scheme
  let Q := D.poincareAt m
  let R : Line.Bundles.LineBundle (B ⊗ B).left :=
    (D.pullback b).poincareAt ((Over.pullback b).map m)
  have hQ : Polarization.FiberComparison.polarizationBiextensionMap D m b =
      r ≫ (Picard.PicardSheaf.familySchemeFunctor A.scheme).map m := by
    have h := Picard.PoincareBundle.Field.ProductBaseChange.poincare_square b D m
    rw [tensorHom_id] at h
    exact h
  let eQ : R.sheaf ≅ (Scheme.Modules.pullback r).obj Q.sheaf :=
    Polarization.BiextensionPoincarePoint.polarizationBiextensionAt_poincareAtIso D m b ≪≫
      (Scheme.Modules.pullbackCongr hQ).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackComp r ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map m)).symm.app
        D.poincare.sheaf
  let M := (L.pullback (fst A.scheme A.scheme).left).sheaf
  let N := (L.pullback (snd A.scheme A.scheme).left).sheaf
  let e₁ := Picard.PoincareBundle.PositiveFormulaAffineSquare.squareIso
    (fst B B).left q r (fst A.scheme A.scheme).left
    (Picard.PoincareBundle.Field.ProductBaseChange.first b A.scheme).symm L.sheaf
  let e₂ := Picard.PoincareBundle.PositiveFormulaAffineSquare.squareIso
    (snd B B).left q r (snd A.scheme A.scheme).left
    (Picard.PoincareBundle.Field.ProductBaseChange.second b A.scheme).symm L.sheaf
  exact Tensor.ProductSheaf.tensorModuleCongr
      (Tensor.ProductSheaf.tensorModuleCongr eQ e₁ ≪≫
        (Picard.Homomorphisms.SchemePullback.Construction.tensorModuleArbitraryPullbackIso r Q.sheaf M).symm) e₂ ≪≫
    (Picard.Homomorphisms.SchemePullback.Construction.tensorModuleArbitraryPullbackIso r (Tensor.ProductSheaf.tensorModule Q.sheaf M) N).symm ≪≫
    (Scheme.Modules.pullback r).mapIso e ≪≫
    Picard.PoincareBundle.PositiveFormulaAffineSquare.squareIso
      r μ[A.scheme].left μ[B].left q
      (Picard.PoincareBundle.Field.ProductBaseChange.multiplication b A.scheme) L.sheaf

/-- Transport an inducing tensor formula along an actual line isomorphism. -/
def Rational.DivisorPolarization.inducingFormulaLineIso
    {S : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (m : A.scheme ⟶ D.abelian.scheme)
    {L M : Line.Bundles.LineBundle A.scheme.left} (a : L.sheaf ≅ M.sheaf)
    (e : (((D.poincareAt m).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf) :
    (((D.poincareAt m).tensor (M.pullback (fst A.scheme A.scheme).left)).tensor
      (M.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (M.pullback μ[A.scheme].left).sheaf :=
  Tensor.ProductSheaf.tensorModuleCongr
    (Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _)
      ((Scheme.Modules.pullback (fst A.scheme A.scheme).left).mapIso a.symm))
    ((Scheme.Modules.pullback (snd A.scheme A.scheme).left).mapIso a.symm) ≪≫
      e ≪≫ (Scheme.Modules.pullback μ[A.scheme].left).mapIso a

/-- Over a field, removing the line at zero preserves ampleness. -/
theorem Rational.DivisorPolarization.zeroNormalizedBundle_isAmple_overField
    {K : Type u} [Field K] {g : ℕ} (A : Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    (L : Line.Bundles.LineBundle A.scheme.left) (hL : L.IsAmple) :
    (A.zeroNormalizedBundle L).IsAmple := by
  let e : (A.zeroNormalizedBundle L).sheaf ≅ L.sheaf :=
    Line.Bundles.LineBundle.sectionNormalized_fixedIso A.scheme.hom η[A.scheme].left L
      (Quotients.FiniteDescent.LineTrivializationOf.Construction.LineTrivialization.pullback_trivial_over_field η[A.scheme].left L)
  exact hL.of_iso e.symm

/-- The graph comparison supplies an ample graph line; divisibility
supplies its symmetry. Together they give the original positive formula. -/
theorem Rational.DivisorPolarization.positiveFormula_of_rational_divisor_graphPower
    {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
    (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
    (qK : Spec (.of K) ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
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
    exact DividedPolarizationSymmetry.rational_divisor_pair_symmetric D p qK (2 * d)
      (Nat.mul_pos (by decide) hd) m L e hp x y
  let c : ℚ →+* K := (Scheme.ΓSpecIso (.of K)).hom.hom.comp
    (qK.appTop.hom.comp (Scheme.ΓSpecIso (.of ℚ)).inv.hom)
  let : Algebra ℚ K := c.toAlgebra
  let : CharZero K := Algebra.charZero_of_charZero ℚ K
  exact SymmetricAmpleGraphPositivity.positiveFormula_of_symmetric_ample_graph D p hs two_ne_zero hG

/-- The original positivity condition on a geometric fiber, using the
actual pullback of the inducing line and the actual graph comparison. -/
theorem Rational.DivisorPolarization.positiveOnGeometricFiber_of_rational_divisor_graphPower
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
    (qS : S ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
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
  have hpos := Rational.DivisorPolarization.positiveFormula_of_rational_divisor_graphPower E p' (s ≫ qS) d hd
    m' L' hL (Rational.DivisorPolarization.inducingFormulaBaseChangeIso D m L e s) hp' eG'
  exact Picard.PoincareBundle.PositiveFormulaIsomorphism.of_iso B.scheme
    (E.poincareAt p') (PolarizationData.polarizationBiextensionAt D p s)
    (Polarization.BiextensionPoincarePoint.polarizationBiextensionAt_poincareAtIso D p s) hpos

/-- Assemble the original polarization from its original isogeny and
kernel type, with positivity proved from the relatively ample graph power. -/
def PolarizationData.Polarization.ofRationalDivisorGraphPower
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (qS : S ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsRelativelyAmple A.scheme.hom)
    (e : (((D.poincareAt m).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)
    (hp : A.multiplication (2 * d) ≫ p.hom = m)
    (eG : (A.zeroNormalizedBundle L).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle D p.hom).tensorPower d).sheaf) : PolarizationData.Polarization D δ where
  isogeny := p
  kernelType := hδ
  positive K _ _ s := Rational.DivisorPolarization.positiveOnGeometricFiber_of_rational_divisor_graphPower
    D p.hom qS d hd m L e hp eG K s
      (hL.isAmple_after_affine_cartesian (IsPullback.of_hasPullback A.scheme.hom s))

/-- Absolute ampleness also suffices, over an arbitrary rational base. -/
def PolarizationData.Polarization.ofAmpleRationalDivisorGraphPower
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (qS : S ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
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
    exact Rational.DivisorPolarization.positiveOnGeometricFiber_of_rational_divisor_graphPower
      D p.hom qS d hd m L e hp eG K s
        (hL.pullback_of_isAffineHom (pullback.fst A.scheme.hom s))

/-- A divisor and graph comparison on any test-scheme base change of an
ample affine-base family give a polarization on that test scheme. -/
def PolarizationData.Polarization.ofBaseChangedRationalDivisorGraphPower
    {S T : Scheme} [IsAffine S] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (b : T ⟶ S)
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback b) (D.abelian.pullback b))
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (qS : S ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsAmple)
    (e : (((D.poincareAt m).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)
    (hp : (A.pullback b).multiplication (2 * d) ≫ p.hom = (Over.pullback b).map m)
    (eG : ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom b)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback b) p.hom).tensorPower d).sheaf) :
    PolarizationData.Polarization (D.pullback b) δ :=
  PolarizationData.Polarization.ofRationalDivisorGraphPower (D.pullback b) p δ hδ (b ≫ qS) d hd
    ((Over.pullback b).map m) (L.pullback (pullback.fst A.scheme.hom b))
    (hL.relativelyAmple_after_baseChange (IsPullback.of_hasPullback A.scheme.hom b))
    (Rational.DivisorPolarization.inducingFormulaBaseChangeIso D m L e b) hp
    ((A.zeroNormalizedBundle_baseChangeIso L b).symm ≪≫ eG)

/-- Positivity from the inducing formula on the zero-normalized line.
Only the original line is required to be ample on this fiber. -/
theorem Rational.DivisorPolarization.positiveOnGeometricFiber_of_normalized_rational_divisor_graphPower
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
    (qS : S ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
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
  exact Rational.DivisorPolarization.positiveOnGeometricFiber_of_rational_divisor_graphPower
    D p qS d hd m (A.zeroNormalizedBundle L) e hp (a ≪≫ eG) K s hN

/-- A relatively ample original line with its actual normalized inducing
formula gives the original polarization. -/
def PolarizationData.Polarization.ofNormalizedRationalDivisorGraphPower
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (qS : S ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
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
  positive K _ _ s := Rational.DivisorPolarization.positiveOnGeometricFiber_of_normalized_rational_divisor_graphPower
    D p.hom qS d hd m L e hp eG K s
      (hL.isAmple_after_affine_cartesian (IsPullback.of_hasPullback A.scheme.hom s))

/-- Absolute ampleness of the original line suffices for the normalized
inducing formula over an arbitrary rational base. -/
def PolarizationData.Polarization.ofAmpleNormalizedRationalDivisorGraphPower
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (qS : S ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
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
    exact Rational.DivisorPolarization.positiveOnGeometricFiber_of_normalized_rational_divisor_graphPower
      D p.hom qS d hd m L e hp eG K s
        (hL.pullback_of_isAffineHom (pullback.fst A.scheme.hom s))

/-- The raw normalized graph-power comparison on any test scheme is
enough; no ampleness of the normalized line over that test is assumed. -/
def PolarizationData.Polarization.ofBaseChangedNormalizedRationalDivisorGraphPower
    {S T : Scheme} [IsAffine S] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (b : T ⟶ S)
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback b) (D.abelian.pullback b))
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (qS : S ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
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
  PolarizationData.Polarization.ofNormalizedRationalDivisorGraphPower (D.pullback b) p δ hδ (b ≫ qS) d hd
    ((Over.pullback b).map m) (L.pullback (pullback.fst A.scheme.hom b))
    (hL.relativelyAmple_after_baseChange (IsPullback.of_hasPullback A.scheme.hom b))
    (Rational.DivisorPolarization.inducingFormulaLineIso (D.pullback b) ((Over.pullback b).map m)
      (A.zeroNormalizedBundle_baseChangeIso L b)
      (Rational.DivisorPolarization.inducingFormulaBaseChangeIso D m (A.zeroNormalizedBundle L) e b)) hp
    ((A.zeroNormalizedBundle_baseChangeIso L b).symm ≪≫ eG)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
