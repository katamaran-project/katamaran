open Interface

type __ = Obj.t

type modality_action =
| MIEnvIsEmpty of bi
| MIEnvForall
| MIEnvTransform of bi
| MIEnvClear of bi
| MIEnvId

type modality = { modality_car : (__ -> __);
                  modality_intuitionistic_action : modality_action;
                  modality_spatial_action : modality_action }
