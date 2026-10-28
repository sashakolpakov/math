import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.EmbeddingCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.OperationsIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.GroupObjectClassifier

/-! # Presented Group Graph Bounds -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresentedGroupGraphBounds

noncomputable section

/-! The prescribed multiplication and inversion Hilbert bounds form a
property of a group-operation diagram in a projective presentation. This
property survives an isomorphism preserving the original embedding. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance presentedGroupProductFlat {S : Scheme.{u}} (X Y : Over S) [Flat X.hom] [Flat Y.hom] :
    Flat (X ⊗ Y).hom := inferInstanceAs (Flat (CategoryTheory.Limits.pullback.fst X.hom Y.hom ≫ X.hom))

local instance presentedGroupProductFinitePresentation {S : Scheme.{u}} (X Y : Over S)
    [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom] :
    LocallyOfFinitePresentation (X ⊗ Y).hom := inferInstanceAs
      (LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.fst X.hom Y.hom ≫ X.hom))

private def tensorPairMap {C : Type*} [Category C] [MonoidalCategory C]
    {X Y Z Z' W : C} (i : X ⟶ Z) (j : Y ⟶ Z') (t : Z ⊗ Z' ⟶ W) : X ⊗ Y ⟶ W :=
  (i ⊗ₘ j) ≫ t

private theorem tensorPairMap_closed {S : Scheme.{u}} {X Y Z Z' W : Over S}
    (i : X ⟶ Z) (j : Y ⟶ Z') (t : Z ⊗ Z' ⟶ W)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left] [ht : IsClosedImmersion t.left] :
    IsClosedImmersion (tensorPairMap i j t).left :=
  @IsClosedImmersion.comp _ _ _ _ _ (Projective.Products.overTensorMap_closed i j) ht

private theorem tensorPairMap_compatible {C : Type*} [Category C] [MonoidalCategory C]
    {X X' Y Y' Z Z' W : C} (a : X ⟶ X') (b : Y ⟶ Y')
    (i : X ⟶ Z) (j : Y ⟶ Z') (i' : X' ⟶ Z) (j' : Y' ⟶ Z')
    (t : Z ⊗ Z' ⟶ W) (hi : a ≫ i' = i) (hj : b ≫ j' = j) :
    (a ⊗ₘ b) ≫ tensorPairMap i' j' t = tensorPairMap i j t := by
  unfold tensorPairMap
  rw [← Category.assoc, tensorHom_comp_tensorHom, hi, hj]

private def productEmbedding {S : Scheme.{u}} {X Y : Over S} {n m : ℕ}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S m) :
    X ⊗ Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S (Affine.SegreOver.segreProjectiveDimension.{u} n m) :=
  Projective.Products.projectiveProductEmbedding i j

private theorem productEmbedding_eq {S : Scheme.{u}} {X Y : Over S} {n m : ℕ}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S m) :
    productEmbedding i j = tensorPairMap i j (Projective.Products.nativeSegreProductEmbedding S n m) := rfl

private instance productEmbedding_closed {S : Scheme.{u}} {X Y : Over S} {n m : ℕ}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S m)
    [hi : IsClosedImmersion i.left] [hj : IsClosedImmersion j.left] :
    IsClosedImmersion (productEmbedding i j).left :=
  Projective.Products.projectiveProductEmbedding_closed i j

private def tensorTripleMap {C : Type*} [Category C] [MonoidalCategory C]
    {X Z W U : C} (i : X ⟶ Z) (s₂ : Z ⊗ Z ⟶ W) (s₃ : W ⊗ Z ⟶ U) :
    (X ⊗ X) ⊗ X ⟶ U :=
  (((i ⊗ₘ i) ≫ s₂) ⊗ₘ i) ≫ s₃

private theorem tensorTripleMap_pair_eq {C : Type*} [Category C] [MonoidalCategory C]
    {X Z W U : C} (i : X ⟶ Z) (s₂ : Z ⊗ Z ⟶ W) (s₃ : W ⊗ Z ⟶ U) :
    tensorTripleMap i s₂ s₃ = tensorPairMap (tensorPairMap i i s₂) i s₃ := rfl

private theorem tensorTripleMap_closed {S : Scheme.{u}} {X Z W U : Over S}
    (i : X ⟶ Z) (s₂ : Z ⊗ Z ⟶ W) (s₃ : W ⊗ Z ⟶ U)
    [IsClosedImmersion i.left] [hs₂ : IsClosedImmersion s₂.left] [hs₃ : IsClosedImmersion s₃.left] :
    IsClosedImmersion (tensorTripleMap i s₂ s₃).left := by
  let : IsClosedImmersion (((i ⊗ₘ i) ≫ s₂).left) :=
    @IsClosedImmersion.comp _ _ _ _ _ (Projective.Products.overTensorMap_closed i i) hs₂
  exact @IsClosedImmersion.comp _ _ _ _ _ (Projective.Products.overTensorMap_closed ((i ⊗ₘ i) ≫ s₂) i) hs₃

private def tripleEmbedding {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) :
    (X ⊗ X) ⊗ X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S
      (Affine.SegreOver.segreProjectiveDimension.{u} (Affine.SegreOver.segreProjectiveDimension.{u} n n) n) :=
  Projective.Products.projectiveProductEmbedding (Projective.Products.projectiveProductEmbedding i i) i

private theorem tripleEmbedding_eq {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) :
    tripleEmbedding i = tensorTripleMap i (Projective.Products.nativeSegreProductEmbedding S n n)
      (Projective.Products.nativeSegreProductEmbedding S (Affine.SegreOver.segreProjectiveDimension.{u} n n) n) := by
  change productEmbedding (productEmbedding i i) i = _
  rw [productEmbedding_eq, productEmbedding_eq]
  exact (tensorTripleMap_pair_eq i (Projective.Products.nativeSegreProductEmbedding S n n)
    (Projective.Products.nativeSegreProductEmbedding S (Affine.SegreOver.segreProjectiveDimension.{u} n n) n)).symm

private instance tripleEmbedding_closed {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [hi : IsClosedImmersion i.left] :
    IsClosedImmersion (tripleEmbedding i).left :=
  @Projective.Products.projectiveProductEmbedding_closed S (X ⊗ X) X
    (Affine.SegreOver.segreProjectiveDimension.{u} n n) n (Projective.Products.projectiveProductEmbedding i i) i
    (Projective.Products.projectiveProductEmbedding_closed i i) hi

private theorem tensorDoubleAndTripleCompatibility {C : Type*} [Category C] [MonoidalCategory C]
    {X Y Z W U : C} (a : X ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (s₂ : Z ⊗ Z ⟶ W) (s₃ : W ⊗ Z ⟶ U) (h : a ≫ j = i) :
    ((a ⊗ₘ a) ≫ ((j ⊗ₘ j) ≫ s₂) = (i ⊗ₘ i) ≫ s₂) ∧
      (((a ⊗ₘ a) ⊗ₘ a) ≫ ((((j ⊗ₘ j) ≫ s₂) ⊗ₘ j) ≫ s₃) =
        (((i ⊗ₘ i) ≫ s₂) ⊗ₘ i) ≫ s₃) := by
  have h₂ : (a ⊗ₘ a) ≫ ((j ⊗ₘ j) ≫ s₂) = (i ⊗ₘ i) ≫ s₂ := by
    rw [← Category.assoc, tensorHom_comp_tensorHom, h]
  refine ⟨h₂, ?_⟩
  rw [← Category.assoc, tensorHom_comp_tensorHom, h₂, h]

private theorem tensorTripleMap_compatible {C : Type*} [Category C] [MonoidalCategory C]
    {X Y Z W U : C} (a : X ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (s₂ : Z ⊗ Z ⟶ W) (s₃ : W ⊗ Z ⟶ U) (h : a ≫ j = i) :
    ((a ⊗ₘ a) ⊗ₘ a) ≫ tensorTripleMap j s₂ s₃ = tensorTripleMap i s₂ s₃ :=
  (tensorDoubleAndTripleCompatibility a i j s₂ s₃ h).2

private theorem tensorTripleIso_compatible
    {C : Type*} [Category C] [MonoidalCategory C] {X Y W : C}
    (e : X ≅ Y) (j : (Y ⊗ Y) ⊗ Y ⟶ W) (i : (X ⊗ X) ⊗ X ⟶ W)
    (h : ((e.hom ⊗ₘ e.hom) ⊗ₘ e.hom) ≫ j = i) :
    ((tensorIso e e).hom ⊗ₘ e.hom) ≫ j = i := by
  simpa only [tensorIso_hom] using h

variable {S : Scheme.{u}} {X Y : Over S}
variable [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated X.hom]

private def multiplicationBound (D : FamilyGroup.Operations.FamilyGroupOperations X)
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (Pm : Polynomial ℚ) : Prop :=
  Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (tripleEmbedding P.embedding) Pm D.mul

private def inversionBound (D : FamilyGroup.Operations.FamilyGroupOperations X)
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (Pi : Polynomial ℚ) : Prop :=
  Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (productEmbedding P.embedding P.embedding) Pi D.inv

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Operations.FamilyGroupOperations.ProjectiveGraphBounds (D : FamilyGroup.Operations.FamilyGroupOperations X)
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (Pm Pi : Polynomial ℚ) : Prop :=
  multiplicationBound D P Pm ∧ inversionBound D P Pi

private theorem graphBounds_mul (D : FamilyGroup.Operations.FamilyGroupOperations X) (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    (Pm Pi : Polynomial ℚ) (hb : D.ProjectiveGraphBounds P Pm Pi) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (tripleEmbedding P.embedding) Pm D.mul := hb.1

private theorem graphBounds_inv (D : FamilyGroup.Operations.FamilyGroupOperations X) (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    (Pm Pi : Polynomial ℚ) (hb : D.ProjectiveGraphBounds P Pm Pi) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (productEmbedding P.embedding P.embedding) Pi D.inv := hb.2

variable [Flat Y.hom] [LocallyOfFinitePresentation Y.hom] [IsSeparated Y.hom]

private theorem groupMulBound_transport
    (D : FamilyGroup.Operations.FamilyGroupOperations X) (e : X ≅ Y) {d : ℕ}
    (i : (X ⊗ X) ⊗ X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S d)
    (j : (Y ⊗ Y) ⊗ Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S d)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (h : ((e.hom ⊗ₘ e.hom) ⊗ₘ e.hom) ≫ j = i)
    (P : Polynomial ℚ) (hb : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial i P D.mul) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P (D.ofIso e).mul :=
  (Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.transport_iff (tensorIso e e) e D.mul i j h P).mp hb

private theorem groupInvBound_transport
    (D : FamilyGroup.Operations.FamilyGroupOperations X) (e : X ≅ Y) {d : ℕ}
    (i : X ⊗ X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S d) (j : Y ⊗ Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S d)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (h : (e.hom ⊗ₘ e.hom) ≫ j = i)
    (P : Polynomial ℚ) (hb : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial i P D.inv) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P (D.ofIso e).inv :=
  (Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.transport_iff e e D.inv i j h P).mp hb

variable {n : ℕ} (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
variable [IsClosedImmersion i.left] [IsClosedImmersion j.left]
variable (e : X ≅ Y) (h : e.hom ≫ j = i)

include h in
omit [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated X.hom]
  [Flat Y.hom] [LocallyOfFinitePresentation Y.hom] [IsSeparated Y.hom]
  [IsClosedImmersion i.left] [IsClosedImmersion j.left] in
private theorem productEmbeddingCompatible :
    (e.hom ⊗ₘ e.hom) ≫ productEmbedding j j = productEmbedding i i := by
  rw [productEmbedding_eq, productEmbedding_eq]
  exact tensorPairMap_compatible e.hom e.hom i i j j
    (Projective.Products.nativeSegreProductEmbedding S n n) h h

include h in
omit [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated X.hom]
  [Flat Y.hom] [LocallyOfFinitePresentation Y.hom] [IsSeparated Y.hom]
  [IsClosedImmersion i.left] [IsClosedImmersion j.left] in
private theorem tripleEmbeddingCompatible :
    ((e.hom ⊗ₘ e.hom) ⊗ₘ e.hom) ≫ tripleEmbedding j = tripleEmbedding i := by
  rw [tripleEmbedding_eq, tripleEmbedding_eq]
  exact tensorTripleMap_compatible e.hom i j
    (Projective.Products.nativeSegreProductEmbedding S n n)
    (Projective.Products.nativeSegreProductEmbedding S (Affine.SegreOver.segreProjectiveDimension.{u} n n) n) h

include h in
omit [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated X.hom]
  [Flat Y.hom] [LocallyOfFinitePresentation Y.hom] [IsSeparated Y.hom]
  [IsClosedImmersion i.left] [IsClosedImmersion j.left] in
private theorem tripleEmbeddingIsoCompatible :
    ((tensorIso e e).hom ⊗ₘ e.hom) ≫ tripleEmbedding j = tripleEmbedding i :=
  tensorTripleIso_compatible e (tripleEmbedding j) (tripleEmbedding i)
    (tripleEmbeddingCompatible i j e h)

include h in
private abbrev transportedMulBound (D : FamilyGroup.Operations.FamilyGroupOperations X) (P : Polynomial ℚ)
    (hb : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (tripleEmbedding i) P D.mul) := by
  exact (Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.transport_iff (tensorIso e e) e D.mul
    (tripleEmbedding i) (tripleEmbedding j) (tripleEmbeddingIsoCompatible i j e h) P).mp hb

include h in
private abbrev transportedInvBound (D : FamilyGroup.Operations.FamilyGroupOperations X) (P : Polynomial ℚ)
    (hb : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (productEmbedding i i) P D.inv) := by
  exact (Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.transport_iff e e D.inv
    (productEmbedding i i) (productEmbedding j j) (productEmbeddingCompatible i j e h) P).mp hb

include h in
private abbrev transportedGraphBounds_mul (D : FamilyGroup.Operations.FamilyGroupOperations X) (Pm Pi : Polynomial ℚ)
    (hb : D.ProjectiveGraphBounds ⟨n, i, inferInstance⟩ Pm Pi) := by
  have hm := graphBounds_mul D ⟨n, i, inferInstance⟩ Pm Pi hb
  exact transportedMulBound i j e h D Pm hm

include h in
private abbrev transportedGraphBounds_inv (D : FamilyGroup.Operations.FamilyGroupOperations X) (Pm Pi : Polynomial ℚ)
    (hb : D.ProjectiveGraphBounds ⟨n, i, inferInstance⟩ Pm Pi) := by
  have hi := graphBounds_inv D ⟨n, i, inferInstance⟩ Pm Pi hb
  exact transportedInvBound i j e h D Pi hi

include h in
abbrev _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Operations.FamilyGroupOperations.ProjectiveGraphBounds.ofIso
    (D : FamilyGroup.Operations.FamilyGroupOperations X) (Pm Pi : Polynomial ℚ)
    (hb : D.ProjectiveGraphBounds ⟨n, i, inferInstance⟩ Pm Pi) :=
  And.intro (transportedGraphBounds_mul i j e h D Pm Pi hb)
    (transportedGraphBounds_inv i j e h D Pm Pi hb)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresentedGroupGraphBounds
