import OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafTensorHom

/-! # Bilinear Sheafification -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms

noncomputable section

/-! Bilinear maps into a sheaf extend uniquely across sheafification of either input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} {L M N K : X.PresheafOfModules} {P : X.Modules}

def PresheafTensorHom.Construction.PresheafBilinearMap.precomp (b : PresheafTensorHom.Construction.PresheafBilinearMap M N P) (f : L ⟶ M) (g : K ⟶ N) :
    PresheafTensorHom.Construction.PresheafBilinearMap L K P where
  app U := (b.app U).compl₁₂ (f.app (.op U)).hom (g.app (.op U)).hom
  naturality {U V} h l k :=
    (b.naturality h (f.app (.op U) l) (g.app (.op U) k)).trans
      (congrArg₂ (fun (m : M.obj (.op V)) (n : N.obj (.op V)) => b.app V m n)
        (PresheafOfModules.naturality_apply f h.op l).symm
        (PresheafOfModules.naturality_apply g h.op k).symm)

def PresheafTensorHom.Construction.PresheafBilinearMap.flip (b : PresheafTensorHom.Construction.PresheafBilinearMap M N P) : PresheafTensorHom.Construction.PresheafBilinearMap N M P where
  app U := (b.app U).flip
  naturality f n m := b.naturality f m n

def PresheafTensorHom.Construction.PresheafBilinearMap.flipEquiv : PresheafTensorHom.Construction.PresheafBilinearMap M N P ≃ PresheafTensorHom.Construction.PresheafBilinearMap N M P where
  toFun := PresheafTensorHom.Construction.PresheafBilinearMap.flip
  invFun := PresheafTensorHom.Construction.PresheafBilinearMap.flip
  left_inv b := by ext U m n; rfl
  right_inv b := by ext U n m; rfl

theorem BilinearSheafification.Construction.presheafBilinearCurry_precomp_left (b : PresheafTensorHom.Construction.PresheafBilinearMap M N P) (f : L ⟶ M) :
    PresheafTensorHom.Construction.presheafBilinearCurry (b.precomp f (𝟙 N)) = f ≫ PresheafTensorHom.Construction.presheafBilinearCurry b := by
  apply PresheafTensorHom.Construction.presheafBilinearCurryEquiv.symm.injective
  change PresheafTensorHom.Construction.presheafBilinearUncurry (PresheafTensorHom.Construction.presheafBilinearCurry _) = PresheafTensorHom.Construction.presheafBilinearUncurry _
  rw [PresheafTensorHom.Construction.presheafBilinearUncurry_curry]
  ext U l n
  change b.app U (f.app (.op U) l) n = b.app U (M.map (𝟙 U).op (f.app (.op U) l)) n
  rw [op_id, M.map_id]
  rfl

def BilinearSheafification.Construction.moduleSheafify (M : X.PresheafOfModules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M

def BilinearSheafification.Construction.moduleSheafifyUnit (M : X.PresheafOfModules) : M ⟶ (BilinearSheafification.Construction.moduleSheafify M).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app M

def BilinearSheafification.Construction.bilinearSheafifyFirstEquiv (M N : X.PresheafOfModules) (P : X.Modules) :
    PresheafTensorHom.Construction.PresheafBilinearMap (BilinearSheafification.Construction.moduleSheafify M).val N P ≃ PresheafTensorHom.Construction.PresheafBilinearMap M N P :=
  PresheafTensorHom.Construction.presheafBilinearCurryEquiv.trans
    (((SheafOfModules.fullyFaithfulForget X.ringCatSheaf).homEquiv
      (X := BilinearSheafification.Construction.moduleSheafify M) (Y := PresheafHomSheaf.Construction.presheafInternalHom N P)).symm.trans
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
        M (PresheafHomSheaf.Construction.presheafInternalHom N P)).trans PresheafTensorHom.Construction.presheafBilinearCurryEquiv.symm))

theorem BilinearSheafification.Construction.bilinearSheafifyFirstEquiv_apply (M N : X.PresheafOfModules) (P : X.Modules)
    (b : PresheafTensorHom.Construction.PresheafBilinearMap (BilinearSheafification.Construction.moduleSheafify M).val N P) :
    BilinearSheafification.Construction.bilinearSheafifyFirstEquiv M N P b = b.precomp (BilinearSheafification.Construction.moduleSheafifyUnit M) (𝟙 N) := by
  apply PresheafTensorHom.Construction.presheafBilinearCurryEquiv.injective
  change PresheafTensorHom.Construction.presheafBilinearCurry (PresheafTensorHom.Construction.presheafBilinearUncurry
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
        M (PresheafHomSheaf.Construction.presheafInternalHom N P) ⟨PresheafTensorHom.Construction.presheafBilinearCurry b⟩)) =
    PresheafTensorHom.Construction.presheafBilinearCurry (b.precomp (BilinearSheafification.Construction.moduleSheafifyUnit M) (𝟙 N))
  erw [PresheafTensorHom.Construction.presheafBilinearCurry_uncurry, BilinearSheafification.Construction.presheafBilinearCurry_precomp_left,
    Adjunction.homEquiv_unit]
  rfl

def BilinearSheafification.Construction.bilinearSheafifyEquiv (M N : X.PresheafOfModules) (P : X.Modules) :
    PresheafTensorHom.Construction.PresheafBilinearMap (BilinearSheafification.Construction.moduleSheafify M).val (BilinearSheafification.Construction.moduleSheafify N).val P ≃
      PresheafTensorHom.Construction.PresheafBilinearMap M N P :=
  (BilinearSheafification.Construction.bilinearSheafifyFirstEquiv M (BilinearSheafification.Construction.moduleSheafify N).val P).trans
    (PresheafTensorHom.Construction.PresheafBilinearMap.flipEquiv.trans
      ((BilinearSheafification.Construction.bilinearSheafifyFirstEquiv N M P).trans PresheafTensorHom.Construction.PresheafBilinearMap.flipEquiv))

theorem BilinearSheafification.Construction.bilinearSheafifyEquiv_apply (M N : X.PresheafOfModules) (P : X.Modules)
    (b : PresheafTensorHom.Construction.PresheafBilinearMap (BilinearSheafification.Construction.moduleSheafify M).val (BilinearSheafification.Construction.moduleSheafify N).val P) :
    BilinearSheafification.Construction.bilinearSheafifyEquiv M N P b = b.precomp (BilinearSheafification.Construction.moduleSheafifyUnit M) (BilinearSheafification.Construction.moduleSheafifyUnit N) := by
  change (BilinearSheafification.Construction.bilinearSheafifyFirstEquiv N M P ((BilinearSheafification.Construction.bilinearSheafifyFirstEquiv M _ P b).flip)).flip = _
  rw [BilinearSheafification.Construction.bilinearSheafifyFirstEquiv_apply, BilinearSheafification.Construction.bilinearSheafifyFirstEquiv_apply]
  ext U m n
  rfl

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms
