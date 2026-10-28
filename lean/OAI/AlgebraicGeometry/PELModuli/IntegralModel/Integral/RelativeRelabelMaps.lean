import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Automorphisms

/-! # Relative Relabel Maps -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

section

/-! Locally varying auxiliary labels on reduced tests, constructed
by actual integral PEL classification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

def IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelAt {T : Over (Spec (.of R))} [IsReduced T.left] (f : T ⟶ X)
    (b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L)) : T ⟶ X :=
  U.classifyingMap hU T ((U.pullback f).relabelAuxiliary b)

def IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelAtComparison {T : Over (Spec (.of R))} [IsReduced T.left] (f : T ⟶ X)
    (b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L)) :
    IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback (U.auxiliaryRelabelAt hU f b)) ((U.pullback f).relabelAuxiliary b) :=
  U.classifyingIso hU T ((U.pullback f).relabelAuxiliary b)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelAt_one {T : Over (Spec (.of R))} [IsReduced T.left] (f : T ⟶ X) :
    U.auxiliaryRelabelAt hU f 1 = f := by
  symm
  exact U.classifying_unique hU T _ f (IntegralAdded.PELId.IntegralAddedPELLevel.Iso.ofEq (U.pullback f).relabelAuxiliary_one.symm)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelAt_mul {T : Over (Spec (.of R))} [IsReduced T.left] (f : T ⟶ X)
    (b c : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L)) :
    U.auxiliaryRelabelAt hU (U.auxiliaryRelabelAt hU f b) c = U.auxiliaryRelabelAt hU f (b * c) :=
  U.classifying_unique hU T _ _ ((U.auxiliaryRelabelAtComparison hU _ c).trans
    (((U.auxiliaryRelabelAtComparison hU f b).relabelAuxiliary c).trans
      (IntegralAdded.PELId.IntegralAddedPELLevel.Iso.ofEq ((U.pullback f).relabelAuxiliary_mul b c))))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelAt_const [IsReduced X.left]
    {T : Over (Spec (.of R))} [IsReduced T.left] (f : T ⟶ X)
    (σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L) :
    U.auxiliaryRelabelAt hU f (LocallyConstant.const _ σ) = f ≫ U.auxiliaryRelabelMap hU σ :=
  (U.classifying_unique hU T _ _ (U.auxiliaryRelabelPullbackComparison hU f σ)).symm

end

/-! The constructed relative auxiliary action commutes with maps
between all reduced tests. The proof retains actual family comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

def IntegralAdded.PELId.IntegralAddedPELLevel.relabelPullbackComparison {T W : Over (Spec (.of R))} (f : T ⟶ X) (a : W ⟶ T)
    (b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L)) :
    IntegralAdded.PELId.IntegralAddedPELLevel.Iso (((U.pullback f).relabelAuxiliary b).pullback a)
      ((U.pullback (a ≫ f)).relabelAuxiliary (b.comap ⟨a.left, a.left.continuous⟩)) :=
  (IntegralAdded.PELId.IntegralAddedPELLevel.Iso.ofEq ((U.pullback f).relabelAuxiliary_pullback b a)).trans
    ((U.pullbackCompIso f a).relabelAuxiliary (b.comap ⟨a.left, a.left.continuous⟩))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelAt_natural (hU : U.IsFine)
    {T W : Over (Spec (.of R))} [IsReduced T.left] [IsReduced W.left]
    (a : W ⟶ T) (f : T ⟶ X) (b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L)) :
    a ≫ U.auxiliaryRelabelAt hU f b =
      U.auxiliaryRelabelAt hU (a ≫ f) (b.comap ⟨a.left, a.left.continuous⟩) :=
  U.classifying_unique hU W _ _
    ((U.pullbackCompIso (U.auxiliaryRelabelAt hU f b) a).symm.trans
      (((U.auxiliaryRelabelAtComparison hU f b).pullback a).trans
        (U.relabelPullbackComparison f a b)))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
