import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackLevelCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterPullbackCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementBaseChange

/-! # Level Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelIso

noncomputable section

/-! Original full-level family isomorphisms with their embedding
identities, composed before specializing the parameter schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def abelianProjectiveBaseChange {S T : Scheme.{u}} {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (f : T ⟶ S) :
    Projective.ProjectivePresentations.ProjectivePresentation (A.pullback f).scheme := P.baseChange f

def abelianProjectiveBaseChangeEmbedding {S T : Scheme.{u}} {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (f : T ⟶ S) :
    (A.pullback f).scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T P.dimension :=
  (P.baseChange f).embedding

structure EmbeddedFullLevelIso {S : Scheme.{u}} {g N : ℕ}
    (A B : Abelian.Schemes.AbelianScheme g S) (l : A.FullLevel N) (k : B.FullLevel N)
    {Z : Scheme.{u}} (i : A.scheme.left ⟶ Z) (j : B.scheme.left ⟶ Z) where
  iso : A.scheme ≅ B.scheme
  group : IsMonHom iso.hom
  level_eq :
    let _ : IsMonHom iso.hom := group
    l.transport iso = k
  embedding_eq : iso.hom.left ≫ j = i

def EmbeddedFullLevelIso.trans {S : Scheme.{u}} {g N : ℕ}
    {A B C : Abelian.Schemes.AbelianScheme g S} {l : A.FullLevel N} {k : B.FullLevel N} {m : C.FullLevel N}
    {Z : Scheme.{u}} {i : A.scheme.left ⟶ Z} {j : B.scheme.left ⟶ Z} {q : C.scheme.left ⟶ Z}
    (E : EmbeddedFullLevelIso A B l k i j) (F : EmbeddedFullLevelIso B C k m j q) :
    EmbeddedFullLevelIso A C l m i q := by
  let : IsMonHom E.iso.hom := E.group
  let : IsMonHom F.iso.hom := F.group
  exact {
    iso := E.iso ≪≫ F.iso
    group := by
      change IsMonHom (E.iso.hom ≫ F.iso.hom)
      infer_instance
    level_eq := (Abelian.Schemes.AbelianScheme.FullLevel.transport_trans E.iso F.iso l).symm.trans
      ((congrArg (fun t : B.FullLevel N => t.transport F.iso) E.level_eq).trans F.level_eq)
    embedding_eq := by
      change (E.iso.hom.left ≫ F.iso.hom.left) ≫ q = i
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun f => E.iso.hom.left ≫ f) F.embedding_eq).trans E.embedding_eq)
  }

def EmbeddedFullLevelIso.precompose {S : Scheme.{u}} {g N : ℕ}
    {A B : Abelian.Schemes.AbelianScheme g S} {l : A.FullLevel N} {k : B.FullLevel N}
    {Z : Scheme.{u}} {i : A.scheme.left ⟶ Z} {j : B.scheme.left ⟶ Z}
    (E : EmbeddedFullLevelIso A B l k i j)
    (C : Abelian.Schemes.AbelianScheme g S) (m : C.FullLevel N)
    (e : C.scheme ≅ A.scheme) [IsMonHom e.hom] (h : m.transport e = l) :
    EmbeddedFullLevelIso C B m k (e.hom.left ≫ i) j :=
  ({ iso := e
     group := inferInstance
     level_eq := h
     embedding_eq := rfl } : EmbeddedFullLevelIso C A m l (e.hom.left ≫ i) i).trans E

def EmbeddedFullLevelRecovery {S : Scheme.{u}} {g N : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (l : A.FullLevel N) (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    {Z : Over S} (i : A.scheme ⟶ Z) (j : F.abelian.scheme ⟶ Z) : Prop :=
  ∃ e : A.scheme ≅ F.abelian.scheme, ∃ h : IsMonHom e.hom, letI := h
    l.transport e = F.level ∧ e.hom ≫ j = i

theorem EmbeddedFullLevelIso.exists_recovery {S : Scheme.{u}} {g N : ℕ}
    {A : Abelian.Schemes.AbelianScheme g S} {l : A.FullLevel N} {F : Level.Data.AbelianSchemeWithFullLevel g N S}
    {Z : Over S} {i : A.scheme ⟶ Z} {j : F.abelian.scheme ⟶ Z}
    (E : EmbeddedFullLevelIso A F.abelian l F.level i.left j.left) :
    EmbeddedFullLevelRecovery A l F i j := by
  refine ⟨E.iso, E.group, E.level_eq, ?_⟩
  exact Over.OverMorphism.ext E.embedding_eq

private theorem inverse_triangle {C : Type*} [Category* C]
    {X Y Z : C} (e : X ≅ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (h : e.inv ≫ i = j) : e.hom ≫ j = i := by
  rw [← h, e.hom_inv_id_assoc]

def parameterPullbackEmbeddedFullLevelIso
    {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (l : A.FullLevel N) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    {U T : Over S} (c : U ⟶ T) :
    EmbeddedFullLevelIso (A.pullback U.hom) ((A.pullback T.hom).pullback c.left)
      (l.pullback U.hom) ((l.pullback T.hom).pullback c.left)
      (abelianProjectiveBaseChange A P U.hom).embedding.left
      (abelianProjectiveBaseChange (A.pullback T.hom)
        (abelianProjectiveBaseChange A P T.hom) c.left).embedding.left where
  iso := A.parameterPullbackIso c
  group := A.parameterPullbackIso_isMonHom c
  level_eq :=
    (Abelian.Schemes.AbelianScheme.FullLevel.transport_eq_iff (A.parameterPullbackIso c) _ _).mpr
      (Abelian.Schemes.AbelianScheme.FullLevel.transport_parameterPullback A c l).symm
  embedding_eq := inverse_triangle ((Over.forget U.left).mapIso (A.parameterPullbackIso c)) _ _
    (Projective.ParameterPullbackCompatibility.ProjectivePullback.parameterPresentationIso_embedding_left P c)

def fullLevelProjectiveBaseChange {S T : Scheme.{u}} {g N : ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N S) (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (f : T ⟶ S) : Projective.ProjectivePresentations.ProjectivePresentation (F.pullback f).abelian.scheme := P.baseChange f

def fullLevelProjectiveBaseChangeEmbedding {S T : Scheme.{u}} {g N : ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N S) (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (f : T ⟶ S) :
    (F.pullback f).abelian.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T P.dimension).left :=
  (fullLevelProjectiveBaseChange F P f).embedding.left

def IteratedFullLevelFamilyRecovery
    {S B C T : Scheme.{u}} {g N : ℕ} (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (p : B ⟶ S) (q : C ⟶ B) (y : T ⟶ S) (a : T ⟶ C) : Prop :=
  ∀ (A : Abelian.Schemes.AbelianScheme g T) (l : A.FullLevel N)
    (e : A.scheme ≅ (F.pullback y).abelian.scheme) [IsMonHom e.hom],
    l.transport e = (F.pullback y).level →
    EmbeddedFullLevelRecovery A l (((F.pullback p).pullback q).pullback a)
      (e.hom ≫ (fullLevelProjectiveBaseChange F P y).embedding)
      (fullLevelProjectiveBaseChange ((F.pullback p).pullback q)
        (fullLevelProjectiveBaseChange (F.pullback p)
          (fullLevelProjectiveBaseChange F P p) q) a).embedding

theorem pointLift_with_fiberProperty {X Y Z : Type*}
    (p : X → Z) (q : X → Y) (c : Z) (y : Y) (Q : Y → X → Prop)
    (h : ∃ x, p x = c ∧ q x = y) (hQ : ∀ x, Q (q x) x) :
    ∃ x, p x = c ∧ Q y x := by
  obtain ⟨x, hp, hq⟩ := h
  exact ⟨x, hp, (congrArg (fun z => Q z x) hq).mp (hQ x)⟩

structure EmbeddedFullLevelFamilyIso {S : Scheme.{u}} {g N : ℕ}
    (F G : Level.Data.AbelianSchemeWithFullLevel g N S)
    {Z : Scheme.{u}} (i : F.abelian.scheme.left ⟶ Z) (j : G.abelian.scheme.left ⟶ Z) where
  data : EmbeddedFullLevelIso F.abelian G.abelian F.level G.level i j

def EmbeddedFullLevelFamilyIso.trans {S : Scheme.{u}} {g N : ℕ}
    {F G H : Level.Data.AbelianSchemeWithFullLevel g N S}
    {Z : Scheme.{u}} {i : F.abelian.scheme.left ⟶ Z} {j : G.abelian.scheme.left ⟶ Z}
    {q : H.abelian.scheme.left ⟶ Z}
    (E : EmbeddedFullLevelFamilyIso F G i j) (K : EmbeddedFullLevelFamilyIso G H j q) :
    EmbeddedFullLevelFamilyIso F H i q := ⟨E.data.trans K.data⟩

def parameterPullbackEmbeddedFullLevelFamilyIso
    {S : Scheme.{u}} {g N : ℕ} (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme) {U T : Over S} (c : U ⟶ T) :
    EmbeddedFullLevelFamilyIso (F.pullback U.hom) ((F.pullback T.hom).pullback c.left)
      (fullLevelProjectiveBaseChangeEmbedding F P U.hom)
      (fullLevelProjectiveBaseChangeEmbedding (F.pullback T.hom)
        (fullLevelProjectiveBaseChange F P T.hom) c.left) :=
  ⟨parameterPullbackEmbeddedFullLevelIso F.abelian F.level P c⟩

structure ParameterPullbackTwiceRecovery
    {S : Scheme.{u}} {g N : ℕ} (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme) {U T : Over S} (c : U ⟶ T)
    {V : Over T.left} (d : Over.mk c.left ⟶ V) where
  data : EmbeddedFullLevelFamilyIso (F.pullback U.hom)
    (((F.pullback T.hom).pullback V.hom).pullback d.left)
    (fullLevelProjectiveBaseChangeEmbedding F P U.hom)
    (fullLevelProjectiveBaseChangeEmbedding ((F.pullback T.hom).pullback V.hom)
      (fullLevelProjectiveBaseChange (F.pullback T.hom)
        (fullLevelProjectiveBaseChange F P T.hom) V.hom) d.left)

def parameterPullbackTwiceRecovery
    {S : Scheme.{u}} {g N : ℕ} (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme) {U T : Over S} (c : U ⟶ T)
    {V : Over T.left} (d : Over.mk c.left ⟶ V) :
    ParameterPullbackTwiceRecovery F P c d where
  data := (parameterPullbackEmbeddedFullLevelFamilyIso F P c).trans
    (parameterPullbackEmbeddedFullLevelFamilyIso (F.pullback T.hom)
      (fullLevelProjectiveBaseChange F P T.hom) d)

namespace ParameterPullbackTwiceRecovery

variable {S : Scheme.{u}} {g N : ℕ} {F : Level.Data.AbelianSchemeWithFullLevel g N S}
    {P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme} {U T : Over S} {c : U ⟶ T}
    {V : Over T.left} {d : Over.mk c.left ⟶ V}
    (E : ParameterPullbackTwiceRecovery F P c d)

abbrev GroupCompatible : Prop := IsMonHom E.data.data.iso.hom

theorem groupCompatible : E.GroupCompatible := E.data.data.group

def LevelCompatible : Prop :=
  letI : IsMonHom E.data.data.iso.hom := E.data.data.group
  (F.pullback U.hom).level.transport E.data.data.iso =
    (((F.pullback T.hom).pullback V.hom).pullback d.left).level

theorem levelCompatible : E.LevelCompatible := E.data.data.level_eq

def NativeEmbeddingCompatible : Prop :=
  E.data.data.iso.hom.left ≫
    fullLevelProjectiveBaseChangeEmbedding ((F.pullback T.hom).pullback V.hom)
      (fullLevelProjectiveBaseChange (F.pullback T.hom)
        (fullLevelProjectiveBaseChange F P T.hom) V.hom) d.left =
    fullLevelProjectiveBaseChangeEmbedding F P U.hom

theorem nativeEmbeddingCompatible : E.NativeEmbeddingCompatible := E.data.data.embedding_eq

def EmbeddingCompatible : Prop :=
  E.data.data.iso.hom ≫
    (fullLevelProjectiveBaseChange ((F.pullback T.hom).pullback V.hom)
      (fullLevelProjectiveBaseChange (F.pullback T.hom)
        (fullLevelProjectiveBaseChange F P T.hom) V.hom) d.left).embedding =
    (fullLevelProjectiveBaseChange F P U.hom).embedding

theorem embeddingCompatible : E.EmbeddingCompatible := by
  apply Over.OverMorphism.ext
  exact E.data.data.embedding_eq

include E in
theorem originalFamilyRecovery :
    IteratedFullLevelFamilyRecovery F P T.hom V.hom U.hom d.left := by
  intro A l e hgroup he
  let : IsMonHom e.hom := hgroup
  exact (E.data.data.precompose A l e he).exists_recovery

end ParameterPullbackTwiceRecovery

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelIso
