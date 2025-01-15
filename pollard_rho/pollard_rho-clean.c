
_Bool pbool(int);

void pact(int);

#define byte char
#define true 1

void mp_factor_using_pollard_rho(void)

{
  pact(0x8f);
  pact(0x90);
  pact(0x91);
  pact(0x92);
  pact(0x8d);
  pact(0x8e);
  if (pbool(0x4a)) {
    pact(0x8c);
  }
  pact(0x8b);
  pact(0x89);
  pact(0x88);
  pact(0x87);
  pact(0x86);
  pact(0x85);
  pact(0x84);
LAB_001000ac:
  if (pbool(0x83)) {
LAB_001000cd:
    pact(0x77);
    pact(0x76);
    pact(0x75);
    pact(0x82);
    pact(0x81);
    pact(0x80);
    if (pbool(0x7f)) {
      pact(0x7e);
      if (pbool(0x7d)) goto LAB_001001e7;
      pact(0x74);
    }
    if (!pbool(0x7c)) {
      pact(0x7b);
      pact(0x7a);
      pact(0x79);
      pact(0x78);
      while (pbool(0x59)) {
        pact(0x77);
        pact(0x76);
        pact(0x75);
        pbool(0xb);
      }
      pact(0x74);
    }
    goto LAB_001000cd;
  }
LAB_001002d4:
  pact(0x61);
  return;
LAB_001001e7:
  do {
    pact(0x73);
    pact(0x72);
    pact(0x71);
    pact(0x6f);
    pact(0x6e);
  } while (pbool(0x6d));
  pact(0x6c);
  if (!pbool(0x6b)) {
    if (pbool(0x4a)) {
      pact(0x6a);
    }
    pact(0x69);
  }
  else {
    pact(0x67);
  }
  if (pbool(0x66)) {
    pact(0x65);
    goto LAB_001002d4;
  }
  pact(100);
  pact(99);
  pact(0x62);
  goto LAB_001000ac;
}

