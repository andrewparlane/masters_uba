generado con:

fnt_cvt.exe -i UbuntuMono-R.ttf -s 30 -a

hay 95 caracteres comenzando con ' ' y terminando con '~'
 !"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~

cada carácter es 16x30 pixeles

UbuntuMono-R.ttf_30_L1.raw es 16x(30*95) = 5700 bytes

inputs offX, offY, char
outputs px
x = offX
y = ((char - ' ') * 30) + offY
px = data(x,y)