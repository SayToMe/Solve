@echo off
cls

dotnet restore

fake build %*