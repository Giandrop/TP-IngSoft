#!/usr/bin/env bash

URL="https://www.clpset.unipr.it/SETLOG/setlog499-1g.zip"
ZIP="setlog499-1g.zip"
DIR="setlog"

# Descargar
echo "Descargando $ZIP..."
wget -O "$ZIP" "$URL"

# Crear directorio destino
mkdir -p "$DIR"

# Extraer
echo "Extrayendo..."
unzip -q "$ZIP" -d "$DIR"

# Borrar zip
echo "Borrando zip..."
rm "$ZIP"

echo "Listo. Archivos en $DIR/"