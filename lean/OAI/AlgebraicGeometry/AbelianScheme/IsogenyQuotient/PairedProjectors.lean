import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Decomposition

/-! # Paired Projectors -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairedProjectors.Construction

noncomputable section

/-!
Group the two halves of the native projector decomposition into paired
blocks. The resulting equivalence remains multiplicative and natural on
every test scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

universe u v

variable {S : Scheme.{u}} {I : Type v}

def pairedBlockPointEquiv (G : I ⊕ I → Over S) [∀ i, GrpObj (G i)] (X : Over S) :
    (∀ i, X ⟶ G i) ≃* (∀ i, X ⟶ G (Sum.inl i) ⊗ G (Sum.inr i)) where
  toFun a i := lift (a (Sum.inl i)) (a (Sum.inr i))
  invFun b j := match j with
    | Sum.inl i => b i ≫ fst (G (Sum.inl i)) (G (Sum.inr i))
    | Sum.inr i => b i ≫ snd (G (Sum.inl i)) (G (Sum.inr i))
  left_inv a := by
    funext i
    cases i with
    | inl i => exact lift_fst _ _
    | inr i => exact lift_snd _ _
  right_inv b := by
    funext i
    apply hom_ext <;> simp only [lift_fst, lift_snd]
  map_mul' a b := by
    funext i
    apply hom_ext <;> simp only [MonObj.mul_comp, lift_fst, lift_snd, Pi.mul_apply]

theorem pairedBlockPointEquiv_naturality (G : I ⊕ I → Over S) [∀ i, GrpObj (G i)]
    {X Y : Over S} (f : X ⟶ Y) (a : ∀ i, Y ⟶ G i) (i : I) :
    pairedBlockPointEquiv G X (fun j => f ≫ a j) i =
      f ≫ pairedBlockPointEquiv G Y a i := by
  exact (comp_lift f (a (Sum.inl i)) (a (Sum.inr i))).symm

variable {T : Over S} [GrpObj T] [IsCommMonObj T] [Fintype I]
  (p : I ⊕ I → (T ⟶ T)) [∀ i, IsMonHom (p i)]
  (horth : ∀ i j, i ≠ j → p i ≫ p j = 1)
  (hcomplete : (∏ i, p i) = 𝟙 T)

abbrev pairedProjectorBlock (i : I) : Over S :=
  BlockGroups.Construction.fixedPointScheme (p (Sum.inl i)) ⊗ BlockGroups.Construction.fixedPointScheme (p (Sum.inr i))

def pairedProjectorPointEquiv (X : Over S) :
    (X ⟶ T) ≃* (∀ i, X ⟶ pairedProjectorBlock p i) :=
  (Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X).trans
    (pairedBlockPointEquiv (fun j => BlockGroups.Construction.fixedPointScheme (p j)) X)

theorem pairedProjectorPointEquiv_naturality
    {X Y : Over S} (f : X ⟶ Y) (x : Y ⟶ T) (i : I) :
    pairedProjectorPointEquiv p horth hcomplete X (f ≫ x) i =
      f ≫ pairedProjectorPointEquiv p horth hcomplete Y x i := by
  change lift (Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X (f ≫ x) (Sum.inl i))
      (Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X (f ≫ x) (Sum.inr i)) = _
  rw [Torsion.Decomposition.Construction.schemeProjectorPointEquiv_naturality, Torsion.Decomposition.Construction.schemeProjectorPointEquiv_naturality]
  exact (comp_lift _ _ _).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairedProjectors.Construction
