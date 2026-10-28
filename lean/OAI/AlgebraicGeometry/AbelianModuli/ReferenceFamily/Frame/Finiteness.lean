import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Map
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Finiteness.LevelCover

noncomputable section

/-! The frame-locus geometry is derived from the actual torsion scheme.
Finite etaleness of torsion is a lower-level hypothesis; no finiteness or
etaleness of the frame scheme is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme}

section Products
variable (X : Over S)

/-- Ordered finite tuples, built by successive fiber products. -/
def pointTuple : ℕ → Over S
  | 0 => Over.mk (𝟙 S)
  | n + 1 => Over.mk (pullback.fst (pointTuple n).hom X.hom ≫ (pointTuple n).hom)

def pointTupleHead (n : ℕ) : LevelCover.pointTuple X (n + 1) ⟶ X :=
  Over.homMk (pullback.snd (LevelCover.pointTuple X n).hom X.hom) pullback.condition.symm

def pointTupleTail (n : ℕ) : LevelCover.pointTuple X (n + 1) ⟶ LevelCover.pointTuple X n :=
  Over.homMk (pullback.fst (LevelCover.pointTuple X n).hom X.hom)

def pointTupleProjection : (n : ℕ) → Fin n → (LevelCover.pointTuple X n ⟶ X)
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases (pointTupleHead X n)
      (fun j => pointTupleTail X n ≫ pointTupleProjection n j) i

def pointTupleLift {T : Over S} : (n : ℕ) → (Fin n → (T ⟶ X)) → (T ⟶ LevelCover.pointTuple X n)
  | 0, _ => Over.homMk T.hom
  | n + 1, v => Over.homMk
      (pullback.lift (pointTupleLift n (fun i => v i.succ)).left (v 0).left (by simp)) (by
        change pullback.lift _ _ _ ≫
          (pullback.fst (LevelCover.pointTuple X n).hom X.hom ≫ (LevelCover.pointTuple X n).hom) = T.hom
        rw [pullback.lift_fst_assoc]
        exact (pointTupleLift n (fun i => v i.succ)).w)

@[simp] theorem pointTupleLift_projection {T : Over S} (n : ℕ) (v : Fin n → (T ⟶ X))
    (i : Fin n) : LevelCover.pointTupleLift X n v ≫ LevelCover.pointTupleProjection X n i = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · apply Over.OverMorphism.ext
      exact pullback.lift_snd _ _ _
    · change LevelCover.pointTupleLift X (n + 1) v ≫
        (pointTupleTail X n ≫ LevelCover.pointTupleProjection X n j) = v j.succ
      rw [← Category.assoc]
      have ht : LevelCover.pointTupleLift X (n + 1) v ≫ pointTupleTail X n =
          LevelCover.pointTupleLift X n (fun i => v i.succ) := by
        apply Over.OverMorphism.ext
        exact pullback.lift_fst _ _ _
      rw [ht]
      exact ih (fun i => v i.succ) j

theorem pointTuple_hom_ext {T : Over S} (n : ℕ) (f h : T ⟶ LevelCover.pointTuple X n)
    (heq : ∀ i, f ≫ LevelCover.pointTupleProjection X n i = h ≫ LevelCover.pointTupleProjection X n i) : f = h := by
  induction n with
  | zero =>
    apply Over.OverMorphism.ext
    exact (Category.comp_id f.left).symm.trans
      (f.w.trans (h.w.symm.trans (Category.comp_id h.left)))
  | succ n ih =>
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congrArg (fun q => q.left) (ih (f ≫ pointTupleTail X n)
        (h ≫ pointTupleTail X n) (fun i => by
          have hi := heq i.succ
          change f ≫ (pointTupleTail X n ≫ LevelCover.pointTupleProjection X n i) =
            h ≫ (pointTupleTail X n ≫ LevelCover.pointTupleProjection X n i) at hi
          simpa only [Category.assoc] using hi))
    · exact congrArg (fun q => q.left) (heq 0)

def pointTupleProductIso (n : ℕ) : LevelCover.pointTuple X n ≅ Limits.piObj (fun _ : Fin n => X) where
  hom := Pi.lift (LevelCover.pointTupleProjection X n)
  inv := LevelCover.pointTupleLift X n (fun i => Pi.π (fun _ : Fin n => X) i)
  hom_inv_id := by
    apply pointTuple_hom_ext
    intro i
    simp only [Category.assoc, pointTupleLift_projection, Pi.lift_comp_π, Category.id_comp]
  inv_hom_id := by
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc, Pi.lift_comp_π, pointTupleLift_projection, Category.id_comp]

theorem pointTuple_etale [Etale X.hom] (n : ℕ) : Etale (LevelCover.pointTuple X n).hom := by
  induction n with
  | zero => change Etale (𝟙 S); infer_instance
  | succ n ih =>
    have := ih
    change Etale (pullback.fst (LevelCover.pointTuple X n).hom X.hom ≫ (LevelCover.pointTuple X n).hom)
    infer_instance

theorem pointTuple_finite [IsFinite X.hom] (n : ℕ) : IsFinite (LevelCover.pointTuple X n).hom := by
  induction n with
  | zero => change IsFinite (𝟙 S); infer_instance
  | succ n ih =>
    have := ih
    change IsFinite (pullback.fst (LevelCover.pointTuple X n).hom X.hom ≫ (LevelCover.pointTuple X n).hom)
    infer_instance

theorem finite_product_etale [Etale X.hom] (n : ℕ) :
    Etale (Limits.piObj (fun _ : Fin n => X)).hom := by
  have := pointTuple_etale X n
  let e := pointTupleProductIso X n
  have : IsIso e.inv.left := inferInstanceAs (IsIso (((Over.forget S).mapIso e).inv))
  rw [← e.inv.w]
  infer_instance

theorem finite_product_finite [IsFinite X.hom] (n : ℕ) :
    IsFinite (Limits.piObj (fun _ : Fin n => X)).hom := by
  have := pointTuple_finite X n
  let e := pointTupleProductIso X n
  have : IsIso e.inv.left := inferInstanceAs (IsIso (((Over.forget S).mapIso e).inv))
  rw [← e.inv.w]
  infer_instance

end Products

/-- Equalizers with an unramified, locally finite-type target are open:
they are base changes of its open diagonal. -/
theorem equalizer_open {X Y : Over S} [FormallyUnramified Y.hom]
    [LocallyOfFiniteType Y.hom] (f h : X ⟶ Y) :
    IsOpenImmersion (equalizer.ι f h).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f h).map (Over.forget _)).flip ?_
  change IsOpenImmersion (Limits.prod.lift (𝟙 Y) (𝟙 Y)).left
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y.hom))
  ext1 <;> simp [← Over.comp_left]

variable {g N : ℕ} (B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def torsionRepresentable : (B.torsionFunctor N ⋙ forget GrpCat).RepresentableBy (Level.Cover.LevelCover.torsion B N) where
  homEquiv := Level.Cover.LevelCover.torsionPointsEquiv B N _
  homEquiv_comp f x := by apply Subtype.ext; exact Category.assoc _ _ _

/-- Identify the equalizer presentation with HilbertConstruction's zero-fiber presentation
using their proved universal properties. -/
def torsionModelIso : Level.Cover.LevelCover.torsion B N ≅ B.torsionScheme N :=
  (LevelCover.torsionRepresentable B).uniqueUpToIso (B.torsionRepresentable N)

theorem torsionTuples_etale [Etale (B.torsionScheme N).hom] : Etale (Level.Cover.LevelCover.torsionTuples B N).hom := by
  let e := torsionModelIso (N := N) B
  have : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget S).mapIso e).hom))
  have : Etale (Level.Cover.LevelCover.torsion B N).hom := by rw [← e.hom.w]; infer_instance
  exact finite_product_etale (Level.Cover.LevelCover.torsion B N) (2 * g)

theorem torsionTuples_finite [IsFinite (B.torsionScheme N).hom] :
    IsFinite (Level.Cover.LevelCover.torsionTuples B N).hom := by
  let e := torsionModelIso (N := N) B
  have : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget S).mapIso e).hom))
  have : IsFinite (Level.Cover.LevelCover.torsion B N).hom := by rw [← e.hom.w]; infer_instance
  exact finite_product_finite (Level.Cover.LevelCover.torsion B N) (2 * g)

/-- Any open frame locus in etale torsion tuples is etale over the base. -/
theorem frameScheme_etale [Etale (B.torsionScheme N).hom] : Etale (Level.Cover.LevelCover.frameScheme B N).hom := by
  have := torsionTuples_etale (N := N) B
  rw [← (Level.Cover.LevelCover.frameInclusion B N).w]
  infer_instance

theorem relation_pow (c : Fin (2 * g) → ZMod N) : Level.Cover.LevelCover.relation B N c ^ N = 1 := by
  unfold Level.Cover.LevelCover.relation
  rw [← Finset.prod_pow]
  have h (i : Fin (2 * g)) : (Level.Cover.LevelCover.coordinate B N i ^ (c i).val) ^ N = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, Level.Cover.LevelCover.coordinate_pow, one_pow]
  simp only [h, Finset.prod_const_one]

def relationTorsion (c : Fin (2 * g) → ZMod N) : Level.Cover.LevelCover.torsionTuples B N ⟶ B.torsionScheme N :=
  (B.torsionSchemePointsEquiv N _).symm ⟨Level.Cover.LevelCover.relation B N c, relation_pow B c⟩

def zeroTorsion : Level.Cover.LevelCover.torsionTuples B N ⟶ B.torsionScheme N :=
  (B.torsionSchemePointsEquiv N _).symm ⟨1, one_pow N⟩

@[simp] theorem relationTorsion_inclusion (c : Fin (2 * g) → ZMod N) :
    relationTorsion B c ≫ B.torsionInclusion N = Level.Cover.LevelCover.relation B N c :=
  congrArg Subtype.val ((B.torsionSchemePointsEquiv N _).apply_symm_apply _)

@[simp] theorem zeroTorsion_inclusion : zeroTorsion (N := N) B ≫ B.torsionInclusion N = 1 :=
  congrArg Subtype.val ((B.torsionSchemePointsEquiv N _).apply_symm_apply _)

/-- The relation locus can be computed inside the finite torsion scheme,
which gives its open as well as its closed nature. -/
def relationZeroTorsionIso (c : Fin (2 * g) → ZMod N) :
    equalizer (Level.Cover.LevelCover.relation B N c) (1 : Level.Cover.LevelCover.torsionTuples B N ⟶ B.scheme) ≅
      equalizer (relationTorsion B c) (zeroTorsion B) where
  hom := equalizer.lift (equalizer.ι (Level.Cover.LevelCover.relation B N c) (1 : Level.Cover.LevelCover.torsionTuples B N ⟶ B.scheme)) (by
    apply (B.torsionSchemePointsEquiv N _).injective
    apply Subtype.ext
    change ((equalizer.ι (Level.Cover.LevelCover.relation B N c) 1 ≫ relationTorsion B c) ≫ B.torsionInclusion N) =
      ((equalizer.ι (Level.Cover.LevelCover.relation B N c) 1 ≫ zeroTorsion B) ≫ B.torsionInclusion N)
    rw [Category.assoc, Category.assoc, relationTorsion_inclusion, zeroTorsion_inclusion]
    exact equalizer.condition _ _)
  inv := equalizer.lift (equalizer.ι (relationTorsion B c) (zeroTorsion B)) (by
    have h := congrArg (fun f => f ≫ B.torsionInclusion N)
      (equalizer.condition (relationTorsion B c) (zeroTorsion B))
    simpa only [Category.assoc, relationTorsion_inclusion, zeroTorsion_inclusion] using h)
  hom_inv_id := by
    apply equalizer.hom_ext
    simp only [Category.assoc, equalizer.lift_ι, Category.id_comp]
  inv_hom_id := by
    apply equalizer.hom_ext
    simp only [Category.assoc, equalizer.lift_ι, Category.id_comp]

theorem relationZeroInclusion_open [Etale (B.torsionScheme N).hom]
    (c : Fin (2 * g) → ZMod N) : IsOpenImmersion (Level.Cover.LevelCover.relationZeroInclusion B N c).left := by
  let e := relationZeroTorsionIso B c
  have : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget S).mapIso e).hom))
  have := equalizer_open (relationTorsion B c) (zeroTorsion B)
  have heOpen : IsOpenImmersion e.hom.left := inferInstance
  have hcomp : IsOpenImmersion
      (e.hom.left ≫ (equalizer.ι (relationTorsion B c) (zeroTorsion B)).left) := inferInstance
  have h : e.hom ≫ equalizer.ι (relationTorsion B c) (zeroTorsion B) =
      Level.Cover.LevelCover.relationZeroInclusion B N c := equalizer.lift_ι _ _
  convert! hcomp using 1
  exact congrArg (fun f => f.left) h.symm

/-- There are only finitely many relation conditions at positive level,
and each is clopen when torsion is etale. -/
theorem frameOpen_isClosed [NeZero N] [Etale (B.torsionScheme N).hom] :
    IsClosed (Level.Cover.LevelCover.frameOpen B N : Set (Level.Cover.LevelCover.torsionTuples B N).left) := by
  unfold Level.Cover.LevelCover.frameOpen
  rw [TopologicalSpace.Opens.coe_iInf]
  apply isClosed_iInter
  intro c
  by_cases hc : c = 0
  · simp [hc]
  · rw [iInf_pos hc]
    have := relationZeroInclusion_open B c
    exact (IsOpenImmersion.isOpen_range (Level.Cover.LevelCover.relationZeroInclusion B N c).left).isClosed_compl

theorem frameInclusion_closed [NeZero N] [Etale (B.torsionScheme N).hom] :
    IsClosedImmersion (Level.Cover.LevelCover.frameInclusion B N).left := by
  apply IsClosedImmersion.of_isPreimmersion
  change IsClosed (Set.range (Level.Cover.LevelCover.frameOpen B N).ι)
  rw [Scheme.Opens.range_ι]
  exact frameOpen_isClosed B

/-- The constructed frame locus is finite etale whenever the actual
torsion kernel is finite etale. This does not assume representability of
the full-level moduli functor. -/
theorem frameScheme_finite_etale [NeZero N]
    [IsFinite (B.torsionScheme N).hom] [Etale (B.torsionScheme N).hom] :
    IsFinite (Level.Cover.LevelCover.frameScheme B N).hom ∧ Etale (Level.Cover.LevelCover.frameScheme B N).hom := by
  have := torsionTuples_finite (N := N) B
  have := frameInclusion_closed (N := N) B
  refine ⟨?_, frameScheme_etale B⟩
  rw [← (Level.Cover.LevelCover.frameInclusion B N).w]
  infer_instance

/-- On a base where a full level is already chosen, the frame locus is
a finite etale surjective cover, with a constructed section. -/
theorem frameScheme_split_cover [NeZero N] (α : B.FullLevel N) :
    IsFinite (Level.Cover.LevelCover.frameScheme B N).hom ∧ Etale (Level.Cover.LevelCover.frameScheme B N).hom ∧
      Surjective (Level.Cover.LevelCover.frameScheme B N).hom := by
  have := α.torsion_finite
  have := α.torsion_etale
  obtain ⟨hf, he⟩ := frameScheme_finite_etale (N := N) B
  exact ⟨hf, he, Map.LevelCover.frame_projection_surjective_of_fullLevel B α⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Finiteness.LevelCover
