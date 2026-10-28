import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ResolutionBasic
import Mathlib.Algebra.Homology.HomotopyCategory

/-! # Resolution Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective

noncomputable section

/- Adapted to HilbertConstruction-local declarations; retain comparison maps and homotopies
for given projective resolutions, with default compilation and elaboration. -/

universe v u

open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C]

open Category Limits Projective

section

variable [HasZeroObject C] [HasZeroMorphisms C]

/-- Auxiliary construction for `lift`. -/
def ResolutionBasic.ProjectiveResolution.liftFZero {Y Z : C} (f : Y ⟶ Z) (P : ResolutionBasic.ProjectiveResolution Y) (Q : ResolutionBasic.ProjectiveResolution Z) [Epi (Q.π.f 0)] :
    P.complex.X 0 ⟶ Q.complex.X 0 := by
  have : Epi (show Q.complex.X 0 ⟶ Z from Q.π.f 0) :=
    inferInstanceAs (Epi (Q.π.f 0))
  exact Projective.factorThru (P.π.f 0 ≫ f) (Q.π.f 0)

@[reassoc (attr := simp)]
lemma ResolutionBasic.ProjectiveResolution.liftFZero_comp {Y Z : C} (f : Y ⟶ Z) (P : ResolutionBasic.ProjectiveResolution Y)
    (Q : ResolutionBasic.ProjectiveResolution Z) [Epi (Q.π.f 0)] :
    ResolutionBasic.ProjectiveResolution.liftFZero f P Q ≫ Q.π.f 0 = P.π.f 0 ≫ f := by
  have : Epi (show Q.complex.X 0 ⟶ Z from Q.π.f 0) :=
    inferInstanceAs (Epi (Q.π.f 0))
  change Projective.factorThru (P.π.f 0 ≫ f)
    (show Q.complex.X 0 ⟶ Z from Q.π.f 0) ≫ Q.π.f 0 = _
  exact Projective.factorThru_comp _ _

end

variable [Abelian C]

lemma ResolutionBasic.ProjectiveResolution.exact₀ {Z : C} (P : ResolutionBasic.ProjectiveResolution Z) :
    (ShortComplex.mk _ _ P.complex_d_comp_π_f_zero).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ P.isColimitCokernelCofork

/-- Auxiliary construction for `lift`. -/
def ResolutionBasic.ProjectiveResolution.liftFOne {Y Z : C} (f : Y ⟶ Z) (P : ResolutionBasic.ProjectiveResolution Y) (Q : ResolutionBasic.ProjectiveResolution Z) :
    P.complex.X 1 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (P.complex.d 1 0 ≫ ResolutionBasic.ProjectiveResolution.liftFZero f P Q) (by erw [Category.assoc, ResolutionBasic.ProjectiveResolution.liftFZero_comp, ← Category.assoc,
      P.complex_d_comp_π_f_zero, zero_comp])

@[simp]
theorem ResolutionBasic.ProjectiveResolution.liftFOne_zero_comm {Y Z : C} (f : Y ⟶ Z) (P : ResolutionBasic.ProjectiveResolution Y)
    (Q : ResolutionBasic.ProjectiveResolution Z) :
    ResolutionBasic.ProjectiveResolution.liftFOne f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ ResolutionBasic.ProjectiveResolution.liftFZero f P Q := by
  apply Q.exact₀.liftFromProjective_comp

/-- Auxiliary construction for `lift`. -/
def ResolutionBasic.ProjectiveResolution.liftFSucc {Y Z : C} (P : ResolutionBasic.ProjectiveResolution Y) (Q : ResolutionBasic.ProjectiveResolution Z) (n : ℕ)
    (g : P.complex.X n ⟶ Q.complex.X n) (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 1))
    (w : g' ≫ Q.complex.d (n + 1) n = P.complex.d (n + 1) n ≫ g) :
    Σ' g'' : P.complex.X (n + 2) ⟶ Q.complex.X (n + 2),
      g'' ≫ Q.complex.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ g' :=
  ⟨(Q.exact_succ n).liftFromProjective
    (P.complex.d (n + 2) (n + 1) ≫ g') (by simp [w]),
      (Q.exact_succ n).liftFromProjective_comp _ _⟩

/-- A morphism in `C` lifts to a chain map between projective resolutions. -/
def ResolutionBasic.ProjectiveResolution.lift {Y Z : C} (f : Y ⟶ Z) (P : ResolutionBasic.ProjectiveResolution Y) (Q : ResolutionBasic.ProjectiveResolution Z) :
    P.complex ⟶ Q.complex :=
  ChainComplex.mkHom _ _ (ResolutionBasic.ProjectiveResolution.liftFZero f _ _) (ResolutionBasic.ProjectiveResolution.liftFOne f _ _) (ResolutionBasic.ProjectiveResolution.liftFOne_zero_comm f P Q)
    fun n ⟨g, g', w⟩ => ⟨(ResolutionBasic.ProjectiveResolution.liftFSucc P Q n g g' w).1, (ResolutionBasic.ProjectiveResolution.liftFSucc P Q n g g' w).2⟩

/-- The resolution maps intertwine the lift of a morphism and that morphism. -/
@[reassoc (attr := simp)]
theorem ResolutionBasic.ProjectiveResolution.lift_commutes {Y Z : C} (f : Y ⟶ Z) (P : ResolutionBasic.ProjectiveResolution Y)
    (Q : ResolutionBasic.ProjectiveResolution Z) : ResolutionBasic.ProjectiveResolution.lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    simp only [HomologicalComplex.comp_f, ResolutionBasic.ProjectiveResolution.lift, ChainComplex.mkHom_f_0,
      ChainComplex.single₀_map_f_zero]
    exact ResolutionBasic.ProjectiveResolution.liftFZero_comp f P Q
  | succ n => simp

@[reassoc (attr := simp)]
lemma ResolutionBasic.ProjectiveResolution.lift_commutes_zero {Y Z : C} (f : Y ⟶ Z)
    (P : ResolutionBasic.ProjectiveResolution Y) (Q : ResolutionBasic.ProjectiveResolution Z) :
    (ResolutionBasic.ProjectiveResolution.lift f P Q).f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f :=
  (HomologicalComplex.congr_hom (ResolutionBasic.ProjectiveResolution.lift_commutes f P Q) 0).trans (by simp)

/-- An auxiliary definition for `liftHomotopyZero`. -/
def ResolutionBasic.ProjectiveResolution.liftHomotopyZeroZero {Y Z : C} {P : ResolutionBasic.ProjectiveResolution Y} {Q : ResolutionBasic.ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : P.complex.X 0 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (f.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]
lemma ResolutionBasic.ProjectiveResolution.liftHomotopyZeroZero_comp {Y Z : C} {P : ResolutionBasic.ProjectiveResolution Y} {Q : ResolutionBasic.ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    ResolutionBasic.ProjectiveResolution.liftHomotopyZeroZero f comm ≫ Q.complex.d 1 0 = f.f 0 :=
  Q.exact₀.liftFromProjective_comp _ _

/-- An auxiliary definition for `liftHomotopyZero`. -/
def ResolutionBasic.ProjectiveResolution.liftHomotopyZeroOne {Y Z : C} {P : ResolutionBasic.ProjectiveResolution Y} {Q : ResolutionBasic.ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    P.complex.X 1 ⟶ Q.complex.X 2 :=
  (Q.exact_succ 0).liftFromProjective (f.f 1 - P.complex.d 1 0 ≫ ResolutionBasic.ProjectiveResolution.liftHomotopyZeroZero f comm)
    (by rw [Preadditive.sub_comp, assoc, HomologicalComplex.Hom.comm,
              ResolutionBasic.ProjectiveResolution.liftHomotopyZeroZero_comp, sub_self])

@[reassoc (attr := simp)]
lemma ResolutionBasic.ProjectiveResolution.liftHomotopyZeroOne_comp {Y Z : C} {P : ResolutionBasic.ProjectiveResolution Y} {Q : ResolutionBasic.ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    ResolutionBasic.ProjectiveResolution.liftHomotopyZeroOne f comm ≫ Q.complex.d 2 1 =
      f.f 1 - P.complex.d 1 0 ≫ ResolutionBasic.ProjectiveResolution.liftHomotopyZeroZero f comm :=
  (Q.exact_succ 0).liftFromProjective_comp _ _

/-- An auxiliary definition for `liftHomotopyZero`. -/
def ResolutionBasic.ProjectiveResolution.liftHomotopyZeroSucc {Y Z : C} {P : ResolutionBasic.ProjectiveResolution Y} {Q : ResolutionBasic.ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (n : ℕ) (g : P.complex.X n ⟶ Q.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    P.complex.X (n + 2) ⟶ Q.complex.X (n + 3) :=
  (Q.exact_succ (n + 1)).liftFromProjective (f.f (n + 2) - P.complex.d _ _ ≫ g') (by simp [w])

@[reassoc (attr := simp)]
lemma ResolutionBasic.ProjectiveResolution.liftHomotopyZeroSucc_comp {Y Z : C} {P : ResolutionBasic.ProjectiveResolution Y} {Q : ResolutionBasic.ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (n : ℕ) (g : P.complex.X n ⟶ Q.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    ResolutionBasic.ProjectiveResolution.liftHomotopyZeroSucc f n g g' w ≫ Q.complex.d (n + 3) (n + 2) =
      f.f (n + 2) - P.complex.d _ _ ≫ g' :=
  (Q.exact_succ (n + 1)).liftFromProjective_comp _ _

/-- Any lift of the zero morphism is homotopic to zero. -/
def ResolutionBasic.ProjectiveResolution.liftHomotopyZero {Y Z : C} {P : ResolutionBasic.ProjectiveResolution Y} {Q : ResolutionBasic.ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : Homotopy f 0 :=
  Homotopy.mkInductive _ (ResolutionBasic.ProjectiveResolution.liftHomotopyZeroZero f comm) (by simp)
    (ResolutionBasic.ProjectiveResolution.liftHomotopyZeroOne f comm) (by simp) fun n ⟨g, g', w⟩ =>
    ⟨ResolutionBasic.ProjectiveResolution.liftHomotopyZeroSucc f n g g' w, by simp⟩

/-- Two lifts of the same morphism are homotopic. -/
def ResolutionBasic.ProjectiveResolution.liftHomotopy {Y Z : C} (f : Y ⟶ Z) {P : ResolutionBasic.ProjectiveResolution Y} {Q : ResolutionBasic.ProjectiveResolution Z}
    (g h : P.complex ⟶ Q.complex) (g_comm : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (ResolutionBasic.ProjectiveResolution.liftHomotopyZero _ (by simp [g_comm, h_comm]))

/-- The lift of the identity morphism is homotopic to the identity chain map. -/
def ResolutionBasic.ProjectiveResolution.liftIdHomotopy (X : C) (P : ResolutionBasic.ProjectiveResolution X) :
    Homotopy (ResolutionBasic.ProjectiveResolution.lift (𝟙 X) P P) (𝟙 P.complex) := by
  apply ResolutionBasic.ProjectiveResolution.liftHomotopy (𝟙 X) <;> simp

/-- The lift of a composition is homotopic to the composition of the lifts. -/
def ResolutionBasic.ProjectiveResolution.liftCompHomotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : ResolutionBasic.ProjectiveResolution X)
    (Q : ResolutionBasic.ProjectiveResolution Y) (R : ResolutionBasic.ProjectiveResolution Z) :
    Homotopy (ResolutionBasic.ProjectiveResolution.lift (f ≫ g) P R) (ResolutionBasic.ProjectiveResolution.lift f P Q ≫ ResolutionBasic.ProjectiveResolution.lift g Q R) := by
  apply ResolutionBasic.ProjectiveResolution.liftHomotopy (f ≫ g) <;> simp

-- We don't care about the actual definitions of these homotopies.
/-- Any two projective resolutions are homotopy equivalent. -/
def ResolutionBasic.ProjectiveResolution.homotopyEquiv {X : C} (P Q : ResolutionBasic.ProjectiveResolution X) :
    HomotopyEquiv P.complex Q.complex where
  hom := ResolutionBasic.ProjectiveResolution.lift (𝟙 X) P Q
  inv := ResolutionBasic.ProjectiveResolution.lift (𝟙 X) Q P
  homotopyHomInvId := (ResolutionBasic.ProjectiveResolution.liftCompHomotopy (𝟙 X) (𝟙 X) P Q P).symm.trans <| by
    simpa [id_comp] using ResolutionBasic.ProjectiveResolution.liftIdHomotopy _ _
  homotopyInvHomId := (ResolutionBasic.ProjectiveResolution.liftCompHomotopy (𝟙 X) (𝟙 X) Q P Q).symm.trans <| by
    simpa [id_comp] using ResolutionBasic.ProjectiveResolution.liftIdHomotopy _ _

@[reassoc (attr := simp)]
theorem ResolutionBasic.ProjectiveResolution.homotopyEquiv_hom_π {X : C} (P Q : ResolutionBasic.ProjectiveResolution X) :
    (ResolutionBasic.ProjectiveResolution.homotopyEquiv P Q).hom ≫ Q.π = P.π := by simp [ResolutionBasic.ProjectiveResolution.homotopyEquiv]

@[reassoc (attr := simp)]
theorem ResolutionBasic.ProjectiveResolution.homotopyEquiv_inv_π {X : C} (P Q : ResolutionBasic.ProjectiveResolution X) :
    (ResolutionBasic.ProjectiveResolution.homotopyEquiv P Q).inv ≫ P.π = Q.π := by simp [ResolutionBasic.ProjectiveResolution.homotopyEquiv]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective
