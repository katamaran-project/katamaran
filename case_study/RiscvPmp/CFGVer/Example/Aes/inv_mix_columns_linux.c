typedef unsigned int u32;
static inline u32 ror32(u32 w, unsigned s){return (w>>s)|(w<<(32-s));}
static u32 mul_by_x(u32 w){u32 x=w&0x7f7f7f7f,y=w&0x80808080;return (x<<1)^(y>>7)*0x1b;}
static u32 mul_by_x2(u32 w){u32 x=w&0x3f3f3f3f,y=w&0x80808080,z=w&0x40404040;return (x<<2)^(y>>7)*0x36^(z>>6)*0x1b;}
static u32 mix_columns(u32 x){u32 y=mul_by_x(x)^ror32(x,16);return y^ror32(x^y,8);}
u32 inv_mix_columns(u32 x){u32 y=mul_by_x2(x);return mix_columns(x^y^ror32(y,16));}
