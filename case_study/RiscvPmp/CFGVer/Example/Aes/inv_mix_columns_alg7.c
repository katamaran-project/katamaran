typedef unsigned int u32;
static inline u32 ror32(u32 w, unsigned s){return (w>>s)|(w<<(32-s));}
/* Value barrier: without it clang -O2 folds Algorithm 7 back into x*y. */
#define OPAQUE(v) __asm__("" : "+r"(v))
/* Algorithm 7 (Grossschaedl-Oswald-Page-Tunstall, ICISC 2009), low 32 bits
   of x*y: y is the operand whose magnitude governs early termination. */
static inline u32 ct_mul(u32 x, u32 y){
  u32 g = (y & 0x00FFFFFF) + 0x01000000; OPAQUE(g);
  u32 t = (y & 0xFF000000) >> 24;        OPAQUE(t);
  u32 p1 = x * g; OPAQUE(p1);
  u32 p2 = x * t; OPAQUE(p2);
  return p1 + (p2 << 24) - (x << 24);
}
static u32 mul_by_x(u32 w){u32 x=w&0x7f7f7f7f,y=w&0x80808080;return (x<<1)^ct_mul(0x1b,y>>7);}
static u32 mul_by_x2(u32 w){u32 x=w&0x3f3f3f3f,y=w&0x80808080,z=w&0x40404040;return (x<<2)^ct_mul(0x36,y>>7)^ct_mul(0x1b,z>>6);}
static u32 mix_columns(u32 x){u32 y=mul_by_x(x)^ror32(x,16);return y^ror32(x^y,8);}
u32 inv_mix_columns(u32 x){u32 y=mul_by_x2(x);return mix_columns(x^y^ror32(y,16));}
