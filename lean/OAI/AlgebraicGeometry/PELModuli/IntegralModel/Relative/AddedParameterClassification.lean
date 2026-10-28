import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.AddedFamily
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FamilyUniqueness

/-! # Added Parameter Classification -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.AddedParameterClassification

noncomputable section

section

/-! Uniqueness for the total two-level PEL parameter combines the pure
classifier with the represented action on its fixed fiber. All comparison
isomorphisms preserve the actual action and both ordered levels. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel (3 * s) P.polarizationType L N M.left)

def relativeAddedPELForget (Z : Over M.left) : (Over.map M.hom).obj Z ⟶ M :=
  Over.homMk Z.hom rfl

theorem relativeAddedPELParameter_classifying_unique
    {Z : Over M.left} (u : (ActionFunctor.relativePELActionFunctor P iotaO M A.auxiliary).obj (op Z))
    (hclass : ∀ (V : Over M.left) [IsReduced V.left], Function.Injective
      (fun f : V ⟶ Z => (ActionFunctor.relativePELActionFunctor P iotaO M A.auxiliary).map f.op u))
    (T : Over (Spec (.of R))) [IsReduced T.left]
    (hFine : ∀ B : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel (3 * s) P.polarizationType L N T.left,
      ∃! f : T ⟶ M, Nonempty (AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso (A.pullback f.left) B))
    (hRigid : ∀ (f : T ⟶ M)
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.auxiliary.pullback f.left) (A.auxiliary.pullback f.left)),
      e.abelian.hom = 𝟙 (A.auxiliary.abelian.pullback f.left).scheme)
    (B : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N T)
    (j k : T ⟶ (Over.map M.hom).obj Z)
    (a : IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((AddedFamily.relativeAddedPELUniversal P iotaO M A Z u).pullback j) B)
    (b : IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((AddedFamily.relativeAddedPELUniversal P iotaO M A Z u).pullback k) B) : j = k := by
  let f := j ≫ relativeAddedPELForget M Z
  let h := k ≫ relativeAddedPELForget M Z
  let aj : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso (A.pullback f.left) B.pure :=
    (AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.pullbackCompIso A Z.hom j.left).symm.trans a.toPure
  let bk : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso (A.pullback h.left) B.pure :=
    (AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.pullbackCompIso A Z.hom k.left).symm.trans b.toPure
  obtain ⟨_, _, hu⟩ := hFine B.pure
  have hh : h = f := (hu h ⟨bk⟩).trans (hu f ⟨aj⟩).symm
  let V : Over M.left := Over.mk f.left
  have : IsReduced V.left := inferInstanceAs (IsReduced T.left)
  let q : V ⟶ Z := Over.homMk j.left rfl
  let r : V ⟶ Z := Over.homMk k.left (congrArg Over.Hom.left hh)
  have he : r = q := FamilyUniqueness.relativePELUniversal_classifying_unique P iotaO M A.auxiliary u
    (hclass V) (hRigid f) r q (b.auxiliary.trans a.auxiliary.symm)
  have hleft : r.left = q.left := congrArg (fun v : V ⟶ Z => v.left) he
  exact Over.OverMorphism.ext hleft.symm

end

/-! The total relative-action parameter classifies the two-level PEL
problem whenever the proved pure classifier and rigidity apply to the
test scheme. This retains the actual universal family and both levels. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel (3 * s) P.polarizationType L N M.left)

theorem relativeAddedPELParameter_classifies
    {Z : Over M.left} (u : (ActionFunctor.relativePELActionFunctor P iotaO M A.auxiliary).obj (op Z))
    (hclass : ∀ (V : Over M.left) [IsReduced V.left], Function.Bijective
      (fun f : V ⟶ Z => (ActionFunctor.relativePELActionFunctor P iotaO M A.auxiliary).map f.op u))
    (T : Over (Spec (.of R))) [IsReduced T.left]
    (hFine : ∀ B : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel (3 * s) P.polarizationType L N T.left,
      ∃! f : T ⟶ M, Nonempty (AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso (A.pullback f.left) B))
    (hRigid : ∀ (f : T ⟶ M)
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.auxiliary.pullback f.left) (A.auxiliary.pullback f.left)),
      e.abelian.hom = 𝟙 (A.auxiliary.abelian.pullback f.left).scheme)
    (B : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N T) :
    ∃! j : T ⟶ (Over.map M.hom).obj Z, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso
      ((AddedFamily.relativeAddedPELUniversal P iotaO M A Z u).pullback j) B) := by
  obtain ⟨f, ⟨e⟩, _⟩ := hFine B.pure
  let t : Over M.left := Over.mk f.left
  have : IsReduced t.left := inferInstanceAs (IsReduced T.left)
  let b : ((Over.map M.hom).obj t) ⟶ T := Over.homMk (𝟙 T.left) (by
    change 𝟙 T.left ≫ T.hom = f.left ≫ M.hom
    exact (Category.id_comp _).trans f.w.symm)
  let B' := B.pullback b
  let e' : AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.Iso (A.pullback t.hom) B'.pure :=
    e.trans (AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.pullbackIdIso B.pure).symm
  obtain ⟨c, ⟨ec⟩⟩ := AddedFamily.relativeAddedPELUniversal_classifying P iotaO M A u (hclass t).surjective B' e'
  let k : T ⟶ (Over.map M.hom).obj Z := Over.homMk c.left (by
    exact (Category.assoc c.left Z.hom M.hom).symm.trans
      ((congrArg (fun m => m ≫ M.hom) c.w).trans f.w))
  let ek : IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((AddedFamily.relativeAddedPELUniversal P iotaO M A Z u).pullback k) B := {
    auxiliary := ec.auxiliary.trans (PEL.Iso.PolarizedActionIso.pullbackId B.auxiliary.data)
    prescribed := (ec.toPure.trans (AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.pullbackIdIso B.pure)).prescribed }
  refine ⟨k, ⟨ek⟩, ?_⟩
  rintro j ⟨ej⟩
  exact relativeAddedPELParameter_classifying_unique P iotaO M A u
    (fun V _ => (hclass V).injective) T hFine hRigid B j k ej ek

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.AddedParameterClassification
