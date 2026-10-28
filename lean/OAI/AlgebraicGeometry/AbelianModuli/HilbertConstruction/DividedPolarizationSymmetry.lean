import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.PairSymmetry
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.RelativePicardInjectivity
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FppfCoverDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GroupDivisionLocus

/-! # Divided Polarization Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DividedPolarizationSymmetry

noncomputable section

/-! Symmetry of an actual divisor of an inducing homomorphism. Equality
descends through the finite flat multiplication map and remains valid on
all test schemes over the field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
universe u

theorem poincarePairClass_symmetric_of_multiple
    {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
    (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
    (n : ℕ) [Flat (A.multiplication n).left]
    [Surjective (A.multiplication n).left]
    [LocallyOfFinitePresentation (A.multiplication n).left]
    (hs : ∀ x y : A.scheme ⊗ A.scheme ⟶ A.scheme,
      D.poincarePairClass (A.scheme ⊗ A.scheme) (x ≫ (p ^ n)) y =
        D.poincarePairClass (A.scheme ⊗ A.scheme) (y ≫ (p ^ n)) x)
    {T : Over (Spec (.of K))} (a b : T ⟶ A.scheme) :
    D.poincarePairClass T (a ≫ p) b = D.poincarePairClass T (b ≫ p) a := by
  let X := A.scheme ⊗ A.scheme
  let x : X ⟶ A.scheme := fst A.scheme A.scheme
  let y : X ⟶ A.scheme := snd A.scheme A.scheme
  let B : Line.Bundles.LineBundle X.left :=
    D.poincarePair (x ≫ p) y
  let C : Line.Bundles.LineBundle X.left :=
    D.poincarePair (y ≫ p) x
  let f := A.multiplication n
  let F : X ⟶ X := f ▷ A.scheme
  have hFx : F ≫ x = x ^ n :=
    (whiskerRight_fst f A.scheme).trans (A.comp_multiplication n x)
  have hFy : F ≫ y = y := whiskerRight_snd f A.scheme
  have hsym : D.poincarePairClass X ((x ^ n) ≫ p) y =
      D.poincarePairClass X (y ≫ p) (x ^ n) := by
    simpa only [MonObj.pow_comp, MonObj.comp_pow, map_pow, MonoidHom.pow_apply] using hs x y
  have hBC : Line.Bundles.LineBundle.pullbackClass F.left (Line.Bundles.LineBundle.classOf B) =
      Line.Bundles.LineBundle.pullbackClass F.left (Line.Bundles.LineBundle.classOf C) := by
    have hB : Line.Bundles.LineBundle.pullbackClass F.left (Line.Bundles.LineBundle.classOf B) =
        D.poincarePairClass X (F ≫ (x ≫ p)) (F ≫ y) :=
      Quotient.sound ⟨D.poincarePairPullbackIso (x ≫ p) y F⟩
    have hC : Line.Bundles.LineBundle.pullbackClass F.left (Line.Bundles.LineBundle.classOf C) =
        D.poincarePairClass X (F ≫ (y ≫ p)) (F ≫ x) :=
      Quotient.sound ⟨D.poincarePairPullbackIso (y ≫ p) x F⟩
    have hB' : D.poincarePairClass X (F ≫ (x ≫ p)) (F ≫ y) =
        D.poincarePairClass X ((x ^ n) ≫ p) y := by
      rw [← Category.assoc, hFx, hFy]
    have hC' : D.poincarePairClass X (F ≫ (y ≫ p)) (F ≫ x) =
        D.poincarePairClass X (y ≫ p) (x ^ n) := by
      rw [← Category.assoc, hFy, hFx]
    exact hB.trans (hB'.trans (hsym.trans (hC'.symm.trans hC.symm)))
  have hPic : (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op A.scheme) (Line.Bundles.LineBundle.classOf B) =
      (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op A.scheme) (Line.Bundles.LineBundle.classOf C) := by
    apply AbelianScheme.CartierDuality.FppfCoverDetection.Construction.Schemes.fppfSheaf_restriction_injective f
      (Picard.PicardSheaf.relativePicardSheaf A.scheme)
    have he : (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op A.scheme)
        (Line.Bundles.LineBundle.pullbackClass F.left (Line.Bundles.LineBundle.classOf B)) =
        (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op A.scheme)
          (Line.Bundles.LineBundle.pullbackClass F.left (Line.Bundles.LineBundle.classOf C)) :=
      congrArg ((Picard.PicardSheaf.toRelativePicard A.scheme).app (.op A.scheme)) hBC
    exact (Picard.PicardSheaf.toRelativePicard_naturality A.scheme f (Line.Bundles.LineBundle.classOf B)).trans
      (he.trans (Picard.PicardSheaf.toRelativePicard_naturality A.scheme f (Line.Bundles.LineBundle.classOf C)).symm)
  let z : A.scheme ⟶ X := lift (𝟙 A.scheme) 1
  have hzx : z ≫ x = 𝟙 A.scheme := lift_fst _ _
  have hzy : z ≫ y = 1 := lift_snd _ _
  let eB : (B.pullback z.left).sheaf ≅ (D.poincarePair p 1).sheaf := by
    simpa only [← Category.assoc, hzx, hzy, Category.id_comp] using
      D.poincarePairPullbackIso (x ≫ p) y z
  let eC : (C.pullback z.left).sheaf ≅
      (D.poincarePair (1 : A.scheme ⟶ D.abelian.scheme) (𝟙 A.scheme)).sheaf := by
    simpa only [← Category.assoc, hzx, hzy, MonObj.one_comp] using
      D.poincarePairPullbackIso (y ≫ p) x z
  let ez : (B.pullback z.left).sheaf ≅ (C.pullback z.left).sheaf :=
    eB ≪≫ D.poincarePair_one_right p ≪≫
      (D.poincarePair_one_left (𝟙 A.scheme)).symm ≪≫ eC.symm
  let : IsReduced A.scheme.left := A.reduced_overField
  let : ConnectedSpace A.scheme.left := A.connected_overField
  obtain ⟨e⟩ := Proper.RelativePicardInjectivity.properField_bundleIso_of_relativePicard_eq A.scheme
    η[A.scheme].left η[A.scheme].w A.scheme B C z.left
    (congrArg Over.Hom.left hzx) ez hPic
  let w : T ⟶ X := lift a b
  have hwx : w ≫ x = a := lift_fst _ _
  have hwy : w ≫ y = b := lift_snd _ _
  let ea : (B.pullback w.left).sheaf ≅ (D.poincarePair (a ≫ p) b).sheaf := by
    simpa only [← Category.assoc, hwx, hwy] using
      D.poincarePairPullbackIso (x ≫ p) y w
  let eb : (C.pullback w.left).sheaf ≅ (D.poincarePair (b ≫ p) a).sheaf := by
    simpa only [← Category.assoc, hwx, hwy] using
      D.poincarePairPullbackIso (y ≫ p) x w
  exact Quotient.sound ⟨ea.symm ≪≫ (Scheme.Modules.pullback w.left).mapIso e ≪≫ eb⟩

theorem rational_divisor_pair_symmetric
    {K : Type} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
    (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
    (qK : Spec (.of K) ⟶ Spec (.of ℚ)) (n : ℕ) (hn : 0 < n)
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (e : (((D.poincareAt m).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)
    (hp : A.multiplication n ≫ p = m)
    {T : Over (Spec (.of K))} (a b : T ⟶ A.scheme) :
    D.poincarePairClass T (a ≫ p) b = D.poincarePairClass T (b ≫ p) a := by
  have hg := Rational.GroupDivisionLocus.rational_multiplication_geometry qK A n hn
  let : Flat (A.multiplication n).left := hg.2.1
  let : Surjective (A.multiplication n).left := hg.2.2.1
  let : LocallyOfFinitePresentation (A.multiplication n).left := hg.2.2.2.1
  have hscalar : A.multiplication n ≫ p = p ^ n := by
    change ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n) ≫ p = p ^ n
    rw [MonObj.pow_comp, Category.id_comp]
  have hm : p ^ n = m := hscalar.symm.trans hp
  refine poincarePairClass_symmetric_of_multiple D p n ?_ a b
  intro x y
  rw [hm]
  exact Polarization.PairSymmetry.polarizationPairClass_symmetric D m L e x y

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DividedPolarizationSymmetry
