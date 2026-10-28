import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Functor

/-! # Classifying -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL

/-! The PEL moduli functor on all test schemes, with its geometric
restriction maps and coherence proved from actual PEL isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
  {T U V : Over (Spec (.of K))}

def Objects.PELIso.pullbackId (A : Objects.PELObject P iota N T) : Objects.PELIso (A.pullback (𝟙 T)) A where
  polarized := HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A.polarized
  action a := by
    change (Over.pullback (𝟙 T.left)).map (A.action.map a) ≫ A.polarized.abelian.pullbackIdIso.hom =
      A.polarized.abelian.pullbackIdIso.hom ≫ A.action.map a
    rw [HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom]
    exact Over.pullbackId.hom.naturality (A.action.map a)

def Objects.PELIso.pullbackComp (A : Objects.PELObject P iota N T) (f : U ⟶ T) (h : V ⟶ U) :
    Objects.PELIso (A.pullback (h ≫ f)) ((A.pullback f).pullback h) where
  polarized := (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A.polarized f.left h.left).symm
  action a := LieBaseChange.action_pullbackComp A.polarized.abelian A.action f.left h.left a

def Objects.PELObject.classOf (A : Objects.PELObject P iota N T) : Objects.PELClasses P iota N T := Quotient.mk _ A

theorem Objects.PELObject.classOf_eq_iff (A B : Objects.PELObject P iota N T) :
    A.classOf = B.classOf ↔ Nonempty (Objects.PELIso A B) := Quotient.eq

def Objects.PELClasses.pullback (f : T ⟶ U) : Objects.PELClasses P iota N U → Objects.PELClasses P iota N T :=
  Quotient.map (fun A => A.pullback f) (fun _ _ ⟨e⟩ => ⟨e.pullback f⟩)

@[simp]
theorem Objects.PELClasses.pullback_classOf (f : T ⟶ U) (A : Objects.PELObject P iota N U) :
    Objects.PELClasses.pullback f A.classOf = (A.pullback f).classOf := rfl

@[simp]
theorem Objects.PELClasses.pullback_id (q : Objects.PELClasses P iota N T) : Objects.PELClasses.pullback (𝟙 T) q = q := by
  induction q using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨Objects.PELIso.pullbackId A⟩

theorem Objects.PELClasses.pullback_comp (f : U ⟶ T) (h : V ⟶ U) (q : Objects.PELClasses P iota N T) :
    Objects.PELClasses.pullback (h ≫ f) q = Objects.PELClasses.pullback h (Objects.PELClasses.pullback f q) := by
  induction q using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨Objects.PELIso.pullbackComp A f h⟩

def Classifying.pelModuliFunctor (P : Datum.RankThreePELDatum E s) (iota : E →+* K) (N : ℕ) :
    (Over (Spec (.of K)))ᵒᵖ ⥤ Type 1 where
  obj T := Objects.PELClasses P iota N T.unop
  map f := TypeCat.ofHom (Objects.PELClasses.pullback f.unop)
  map_id _ := by
    ext q
    exact Objects.PELClasses.pullback_id q
  map_comp f h := by
    ext q
    exact Objects.PELClasses.pullback_comp f.unop h.unop q

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily

/-! Relate the statement's explicit PEL pullback comparison to the
constructed geometric moduli functor. These are the same isomorphism
conditions on the actual families and their normalized Poincare bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
  {T U : Over (Spec (.of K))}

def Models.PELPullbackIso.toPELIso {A : PEL.Objects.PELObject P iota N U} {B : PEL.Objects.PELObject P iota N T}
    {f : T ⟶ U} (e : Models.PELPullbackIso A B f) : PEL.Objects.PELIso B (A.pullback f) where
  polarized := {
    abelian := e.abelian
    dual := e.dual
    abelianGroup := e.abelianGroup
    dualGroup := e.dualGroup
    polarization := e.polarization
    poincare :=
      (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (e.dual.hom ⊗ₘ e.abelian.hom).left
        (A.polarized.dual.poincarePullbackOverMap f.left).left
        (HilbertConstruction.Line.Bundles.LineBundle.classOf A.polarized.dual.poincare)).symm.trans
          ((congrArg (fun q => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
            ((e.dual.hom ⊗ₘ e.abelian.hom).left ≫ q)
            (HilbertConstruction.Line.Bundles.LineBundle.classOf A.polarized.dual.poincare))
            (HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap A.polarized.dual f.left).symm).trans e.poincare)
    level := e.level }
  action := e.action

def Models.PELPullbackIso.ofPELIso {A : PEL.Objects.PELObject P iota N U} {B : PEL.Objects.PELObject P iota N T}
    {f : T ⟶ U} (e : PEL.Objects.PELIso B (A.pullback f)) : Models.PELPullbackIso A B f where
  abelian := e.polarized.abelian
  dual := e.polarized.dual
  abelianGroup := e.polarized.abelianGroup
  dualGroup := e.polarized.dualGroup
  polarization := e.polarized.polarization
  poincare :=
    (congrArg (fun q => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      ((e.polarized.dual.hom ⊗ₘ e.polarized.abelian.hom).left ≫ q)
      (HilbertConstruction.Line.Bundles.LineBundle.classOf A.polarized.dual.poincare))
      (HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap A.polarized.dual f.left)).trans
        ((HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp
          (e.polarized.dual.hom ⊗ₘ e.polarized.abelian.hom).left
          (A.polarized.dual.poincarePullbackOverMap f.left).left
          (HilbertConstruction.Line.Bundles.LineBundle.classOf A.polarized.dual.poincare)).trans e.polarized.poincare)
  level := e.polarized.level
  action := e.action

theorem Models.PELPullbackIso.nonempty_iff_classOf {A : PEL.Objects.PELObject P iota N U}
    {B : PEL.Objects.PELObject P iota N T} (f : T ⟶ U) :
    Nonempty (Models.PELPullbackIso A B f) ↔ B.classOf = (A.pullback f).classOf := by
  rw [PEL.Objects.PELObject.classOf_eq_iff]
  exact ⟨fun ⟨e⟩ => ⟨e.toPELIso⟩, fun ⟨e⟩ => ⟨Models.PELPullbackIso.ofPELIso e⟩⟩

variable (M : Models.FinePELModel P iota N)

/-- The classifying transformation of the actual universal candidate. -/
def Models.FinePELModel.classifying : uliftYoneda.{1}.obj M.space ⟶ PEL.Classifying.pelModuliFunctor P iota N :=
  uliftYonedaEquiv.symm M.universal.classOf

theorem Models.FinePELModel.classifying_apply (T : Over (Spec (.of K))) (f : T ⟶ M.space) :
    M.classifying.app (.op T) (ULift.up f) = (M.universal.pullback f).classOf := rfl

/-- The exact pullback comparison used in ReferenceFamily is equivalent to the
classifying transformation taking the prescribed value. -/
theorem Models.FinePELModel.classifying_eq_iff (T : Over (Spec (.of K))) (B : PEL.Objects.PELObject P iota N T)
    (f : T ⟶ M.space) :
    M.classifying.app (.op T) (ULift.up f) = B.classOf ↔ Nonempty (Models.PELPullbackIso M.universal B f) :=
  eq_comm.trans (Models.PELPullbackIso.nonempty_iff_classOf (A := M.universal) (B := B) f).symm

end AlgebraicGeometry.AbelianModuli.ReferenceFamily

end

end OAI
