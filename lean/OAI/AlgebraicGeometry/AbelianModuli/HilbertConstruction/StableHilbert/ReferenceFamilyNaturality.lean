import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ReferenceFamilyTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ClassifierNaturality

/-! # Reference Family Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ReferenceFamilyNaturality

noncomputable section

/-! Pullback naturality of the global comparison of the original
Hilbert families. The affine specialization is the coordinate-compatible
comparison already used by the bounded group and full-level classifier. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

namespace ParameterConjugation

theorem natural {C : Type*} [Category* C]
    {A B A' B' X Y X' Y' : C}
    (a : A ≅ X) (b : B ≅ Y) (a' : A' ≅ X') (b' : B' ≅ Y')
    (e : A ≅ B) (e' : A' ≅ B')
    (f : A' ⟶ A) (g : B' ⟶ B) (h : X' ⟶ X) (k : Y' ⟶ Y)
    (ha : f ≫ a.hom = a'.hom ≫ h)
    (hb : g ≫ b.hom = b'.hom ≫ k)
    (he : f ≫ e.hom = e'.hom ≫ g) :
    h ≫ (a.symm ≪≫ e ≪≫ b).hom = (a'.symm ≪≫ e' ≪≫ b').hom ≫ k := by
  apply (cancel_epi a'.hom).mp
  have ha' : a'.hom ≫ h ≫ a.inv = f := by
    rw [← Category.assoc, ← ha, Category.assoc, a.hom_inv_id, Category.comp_id]
  calc
    _ = (a'.hom ≫ h ≫ a.inv) ≫ e.hom ≫ b.hom := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    _ = f ≫ e.hom ≫ b.hom := congrArg (fun q => q ≫ e.hom ≫ b.hom) ha'
    _ = e'.hom ≫ (g ≫ b.hom) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ b.hom) he).trans (Category.assoc _ _ _))
    _ = e'.hom ≫ (b'.hom ≫ k) := congrArg (fun q => e'.hom ≫ q) hb
    _ = _ := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, a'.hom_inv_id_assoc]

end ParameterConjugation

private theorem cartesian_iso_conjugation {C : Type*} [Category* C]
    {A B X Y P Q : C} (r : A ≅ X) (s : B ≅ Y)
    (n : A ≅ P) (m : B ≅ Q) (e : P ≅ Q) :
    r.symm ≪≫ n ≪≫ e ≪≫ m.symm ≪≫ s =
      (n.symm ≪≫ r).symm ≪≫ e ≪≫ (m.symm ≪≫ s) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]

private theorem native_embedding_of_iso_eq
    {S W : Scheme.{u}} {X Y : Over S} (e f : X ≅ Y) (h : e = f)
    (i : Y.left ⟶ W) (j : X.left ⟶ W) (a : W ⟶ W)
    (hf : f.hom.left ≫ i = j ≫ a) : e.hom.left ≫ i = j ≫ a :=
  (congrArg (fun q : X ≅ Y => q.hom.left ≫ i) h).trans hf

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))}
    (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (b : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D H = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)

private theorem originalFamilyTransport_eq_cartesian :
    ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD j k a b hab =
      (Intrinsic.ClassifierNaturality.nativeHilbertClassifierCartesianIso n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
        (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H) H
        (ClassifyingMap.stableConfigurationHilbert_canonicalFiberPolynomial R i j D H hH) a).symm ≪≫
      FamilyTransport.stableHilbertFamilyTransport R i D H hH hD j k a b hab ≪≫
      Intrinsic.ClassifierNaturality.nativeHilbertClassifierCartesianIso n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
        (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i k D H) H
        (ClassifyingMap.stableConfigurationHilbert_canonicalFiberPolynomial R i k D H hH) b := by
  exact cartesian_iso_conjugation
    (ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i j D H hH a)
    (ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i k D H hH b)
    (Intrinsic.FamilyPullbackIso.nativeFamilyPullbackIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H))
    (Intrinsic.FamilyPullbackIso.nativeFamilyPullbackIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) b
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i k D H))
    (FamilyTransport.stableHilbertFamilyTransport R i D H hH hD j k a b hab)

/-- The global original-family comparison commutes with every test
base change, with its actual native pullback projections. -/
theorem stableHilbertOriginalFamilyTransport_natural
    {U : Over (Spec (.of R))} (u : U ⟶ T)
    (hu : (u ≫ a) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      (u ≫ b) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H) :
    Single.ParameterBaseChange.singleParameterBaseChangeMap
      (Over.homMk u.left
        (congrArg Over.Hom.left (Category.assoc u a (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)).symm) :
        Over.mk ((u ≫ a) ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left ⟶
          Over.mk (a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left)
      (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H).family.scheme ≫
        (ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD j k a b hab).hom.left =
    (ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD j k (u ≫ a) (u ≫ b) hu).hom.left ≫
      Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk u.left
          (congrArg Over.Hom.left (Category.assoc u b (ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH)).symm) :
          Over.mk ((u ≫ b) ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH).left ⟶
            Over.mk (b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH).left)
        (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H).family.scheme := by
  rw [originalFamilyTransport_eq_cartesian, originalFamilyTransport_eq_cartesian]
  let ca := Intrinsic.ClassifierNaturality.nativeHilbertClassifierCartesianIso n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H) H
    (ClassifyingMap.stableConfigurationHilbert_canonicalFiberPolynomial R i j D H hH) a
  let cb := Intrinsic.ClassifierNaturality.nativeHilbertClassifierCartesianIso n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i k D H) H
    (ClassifyingMap.stableConfigurationHilbert_canonicalFiberPolynomial R i k D H hH) b
  let ca' := Intrinsic.ClassifierNaturality.nativeHilbertClassifierCartesianIso n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H) H
    (ClassifyingMap.stableConfigurationHilbert_canonicalFiberPolynomial R i j D H hH) (u ≫ a)
  let cb' := Intrinsic.ClassifierNaturality.nativeHilbertClassifierCartesianIso n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i k D H) H
    (ClassifyingMap.stableConfigurationHilbert_canonicalFiberPolynomial R i k D H hH) (u ≫ b)
  exact ParameterConjugation.natural
    ((Over.forget T.left).mapIso ca) ((Over.forget T.left).mapIso cb)
    ((Over.forget U.left).mapIso ca') ((Over.forget U.left).mapIso cb')
    ((Over.forget T.left).mapIso (FamilyTransport.stableHilbertFamilyTransport R i D H hH hD j k a b hab))
    ((Over.forget U.left).mapIso (FamilyTransport.stableHilbertFamilyTransport R i D H hH hD j k (u ≫ a) (u ≫ b) hu))
    _ _ _ _
    (Intrinsic.ClassifierNaturality.nativeHilbertClassifierCartesianIso_natural n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H) H
      (ClassifyingMap.stableConfigurationHilbert_canonicalFiberPolynomial R i j D H hH) a u)
    (Intrinsic.ClassifierNaturality.nativeHilbertClassifierCartesianIso_natural n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i k D H) H
      (ClassifyingMap.stableConfigurationHilbert_canonicalFiberPolynomial R i k D H hH) b u)
    (FamilyBaseChange.stableHilbertFamilyTransport_natural R i D H hH hD j k a b hab u hu)

/-- On an affine overlap the same global comparison preserves the
original embeddings by the actual coordinate change. -/
theorem stableHilbertOriginalFamilyTransport_affine_embedding_left
    {C : Type u} [CommRing C] [IsNoetherianRing C]
    {f : Spec (.of C) ⟶ Spec (.of R)}
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D H = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)
    (v : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (ha : a = v ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (hb : b = v ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) :
    (ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD j k a b hab).hom.left ≫
      ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H).baseChange
        (b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH).left).embedding.left =
    ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H).baseChange
        (a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left).embedding.left ≫
      (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k v).hom.left := by
  subst a
  subst b
  exact native_embedding_of_iso_eq _ _
    (ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport_affine R i D H hH hD j k v hab) _ _ _
    (AffineProjectiveEmbedding.StableHilbertAffineTransport.familyIso_embedding_left R i D H hH hD j k v)

theorem stableHilbertOriginalFamilyTransport_affine_embedding
    {C : Type u} [CommRing C] [IsNoetherianRing C]
    {f : Spec (.of C) ⟶ Spec (.of R)}
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D H = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)
    (v : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (ha : a = v ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (hb : b = v ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) :
    (ReferenceFamilyTransport.stableHilbertOriginalFamilyTransport R i D H hH hD j k a b hab).hom ≫
      ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H).baseChange
        (b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH).left).embedding =
    ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H).baseChange
        (a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left).embedding ≫
      (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k v).hom := by
  apply Over.OverMorphism.ext
  exact stableHilbertOriginalFamilyTransport_affine_embedding_left R i D H hH hD j k a b hab v ha hb

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ReferenceFamilyNaturality
